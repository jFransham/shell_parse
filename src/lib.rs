#![feature(box_syntax)]
#![feature(conservative_impl_trait)]

extern crate combine;

use combine::*;
use combine::char::*;
use std::iter;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    FunctionDef(VariableName, Box<Statement>),
    Block(Vec<Statement>),
    FunctionCall(
        Vec<(VariableName, Expression)>,
        Expression,
        Vec<Expression>
    ),
    IfStatement(Box<Statement>, Vec<Statement>),
    WhileStatement(Box<Statement>, Vec<Statement>),
    ForStatement(VariableName, Vec<Expression>, Vec<Statement>),
    SetParameters(Vec<(VariableName, Expression)>),
}

// TODO: Make this Rc<str>
pub type VariableName = String;

#[derive(Debug, Clone, PartialEq)]
pub enum Glob {
    Many,
    One,
}

#[derive(Debug, Clone, PartialEq)]
pub enum VariableReference {
    Magic(MagicVar),
    Ref(VariableName),
}

impl<T: Into<String>> From<T> for VariableReference {
    fn from(other: T) -> Self {
        VariableReference::Ref(other.into())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum MagicVar {
    // $0: The name of the script
    ScriptName,
    // $#: The number of arguments passed to the script or function
    NumArgs,
    // $@: An array of all the arguments passed to the script or function. This
    //     is the only user-visible form of arrays unless I implement the Bash
    //     extension of user-defined arrays
    Arguments,
    // $*: An array of the passed arguments, joined with the first character of
    //     $IFS, as a string
    ArgumentString,
    // $N: Starts from 1 in the script, but 0 internally.
    //     This is because $0 is considered a "special parameter"
    Argument(u32),
    // $_: The last argument of the last command
    LastLastArgument,
    // $?: The exit code of the last pipeline
    LastExitCode,
    // $!: The proc id of the last spawned process
    LastProcId,
    // $$: The proc id of the current shell
    ProcId,
    // $-: The arguments to the current shell (either with `set` or command-
    //     line)
    ShellArgs,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct LookupBehavior {
    if_set:   VariableBehavior,
    if_null:  VariableBehavior,
    if_unset: VariableBehavior,
}

#[derive(Debug, Clone, PartialEq)]
pub enum VariableBehavior {
    /// Raise an error with either an explicit message or the shell's default
    /// (normally, "parameter not set")
    Fail(Option<Rc<Expression>>),
    /// Substitute the value of some expression
    Substitute(Rc<Expression>),
    /// Assign the value of some expression to the parameter
    Assign(Rc<Expression>),
    /// Do whatever the shell's default is
    Inherit,
}

impl Default for VariableBehavior {
    fn default() -> Self {
        VariableBehavior::Inherit
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expression {
    Literal(String),
    Glob(Glob),
    Concat(Vec<Expression>),
    // Ideally convert this to use Rc<str> so we can do simple reference
    // equality
    // TODO: Replace `LookupBehavior` here with `Option<Box<LookupBehaviour>>`
    //       to save space (we allocate so much anyway so the extra box probably
    //       won't matter)
    VariableReference(VariableReference, LookupBehavior),
    Expand(Box<Statement>),
    Escape(Box<Expression>),
}

type RefParse<'a, T, O> = &'a mut (Parser<Input=T, Output=O> + 'a);

fn single_string<R: Stream<Item=char>>(input: R) -> ParseResult<String, R> {
    between(
        token('\''),
        token('\''),
        many(
            choice(
                [
                    &mut try(string("\\'")).map(|_| '\'') as RefParse<R, _>,
                    &mut none_of(iter::once('\'')),
                ]
            )
        )
    ).map(|c: String| c).parse_stream(input)
}

fn comment_or_newline<R: Stream<Item=char>>(
    input: R,
) -> ParseResult<(), R> {
    (
        optional(
            (
                token('#'),
                skip_many(none_of(iter::once('\n'))),
            )
        ),
        token('\n'),
    ).map(|_| ()).parse_stream(input)
}

fn statement_terminator<R: Stream<Item=char>>(
    input: R
) -> ParseResult<(), R> {
    skip_many1(
        try(
            (
                parser(whitespace),
                choice(
                    [
                        &mut parser(comment_or_newline) as RefParse<_, _>,
                        &mut token(';').map(|_| ()),
                    ]
                ),
                parser(whitespace),
            )
        )
    ).parse_stream(input)
}

/// Returns a lazy iterator over statements. This won't execute any code, but
/// may cause unbounded memory usage, so don't use it for untrusted inputs.
///
/// ```rust
/// use shell_parse::{parse_statements, Statement, Expression};
///
/// let test_string = r#"
/// ## Ok guys, here's the plan. We're going to steal all of Google.
/// GOOGLE=$(curl http://google.com); echo $GOOGLE
/// exit 0
/// "#;
/// let mut statements = parse_statements(test_string);
///
/// assert_eq!(
///     statements.next().expect("No statements found!"),
///     Statement::SetParameters(
///         vec![
///             (
///                 "GOOGLE".into(),
///                 Expression::Expand(
///                     Box::new(
///                         Statement::FunctionCall(
///                             vec![],
///                             Expression::Literal("curl".into()),
///                             vec![
///                                 Expression::Literal(
///                                     "http://google.com".into()
///                                 )
///                             ],
///                         )
///                     )
///                 )
///             )
///         ]
///     )
/// );
/// ```
pub fn parse_statements<R: Stream<Item=char>>(
    input: R,
) -> impl Iterator<Item=Statement> {
    struct StatementStream<T>(Option<T>);

    impl<T: Stream<Item=char>> Iterator for StatementStream<T> {
        type Item = Statement;

        fn next(&mut self) -> Option<Statement> {
            let opt = self.0.take();

            if let Some(to_parse) = opt {
                let parsed = (
                    parser(parse_statement),
                    parser(statement_terminator),
                ).parse_stream(to_parse);

                if let Ok(((out, _), rest)) = parsed {
                    self.0 = Some(rest.into_inner());

                    Some(out)
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    let to_first_statement =
        optional(parser(statement_terminator)).parse_stream(input);

    StatementStream(to_first_statement.map(|(_, r)| r.into_inner()).ok())
}

fn is_whitespace_char(c: char) -> bool {
    c.is_whitespace() & (c != '\n')
}

fn escaped_newline<R: Stream<Item=char>>(
    input: R
) -> ParseResult<(), R> {
    try(
        (
            token('\\'),
            token('\n'),
        )
    ).map(|_| ()).parse_stream(input)
}

fn mandatory_whitespace<R: Stream<Item=char>>(input: R) ->
    ParseResult<(), R>
{
    skip_many1(
        choice(
            [
                &mut skip_many1(
                    satisfy(is_whitespace_char)
                ) as RefParse<R, _>,
                &mut skip_many1(
                    parser(escaped_newline)
                ),
            ]
        )
    ).parse_stream(input)
}

fn whitespace<R: Stream<Item=char>>(input: R) ->
    ParseResult<Option<()>, R>
{
    optional(parser(mandatory_whitespace)).parse_stream(input)
}

pub fn parse_statement<R: Stream<Item=char>>(
    input: R,
) -> ParseResult<Statement, R> {
    fn loop_body<R: Stream<Item=char>>(input: R) ->
        ParseResult<Vec<Statement>, R>
    {
        between(
            (
                string("do"),
                optional(parser(statement_terminator)),
                parser(whitespace),
            ),
            string("done"),
            many1(
                try(
                    (
                        parser(parse_statement),
                        parser(statement_terminator),
                    )
                ).map(|(s, _)| s)
            )
        ).parse_stream(input)
    }

    fn func_call<R: Stream<Item=char>>(input: R) ->
        ParseResult<(Expression, Vec<Expression>), R>
    {
        // TODO: Add esac
        let invalid_function_names = [
            try(string("if")),
            try(string("while")),
            try(string("then")),
            try(string("done")),
            try(string("do")),
            try(string("for")),
            try(string("fi")),
        ];

        (
            not_followed_by(
                (
                    choice(invalid_function_names),
                    not_followed_by(satisfy(is_ident)),
                ).map(|(name, _)| name)
            ),
            parser(parse_expression),
            many(
                try(
                    (
                        parser(mandatory_whitespace),
                        parser(parse_expression)
                    )
                ).map(|(_, exp)| exp)
            ),
        ).map(|(_, name, args)| (name, args))
            .parse_stream(input)
    }

    let mut if_statement = (
        try(string("if")),
        parser(mandatory_whitespace),
        parser(parse_statement),
        (parser(statement_terminator), parser(whitespace)),
        between(
            (string("then"), optional(parser(statement_terminator))),
            string("fi"),
            many1(
                try(
                    (
                        parser(parse_statement),
                        parser(statement_terminator),
                    )
                ).map(|(s, _)| s)
            )
        ),
    ).map(
        |(_, _, head, _, body)| Statement::IfStatement(box head, body)
    );

    let mut env_statement = (
        many1(
            try(
                (
                    parser(whitespace),
                    ident(),
                    token('='),
                    parser(parse_expression),
                )
            ).map(|(_, name, _, val)| (name, val))
        ),
        optional(
            (
                parser(mandatory_whitespace),
                parser(func_call),
            ).map(|(_, target)| target)
        ),
    ).map(
        |(vars, opt_stmt): (_, Option<_>)|
        if let Some((head, args)) = opt_stmt {
            Statement::FunctionCall(
                vars,
                head,
                args,
            )
        } else {
            Statement::SetParameters(vars)
        }
    );

    let mut raw_func_call = parser(func_call).map(
        |(head, args)|
        Statement::FunctionCall(vec![], head, args)
    );

    let mut while_statement = (
        try(string("while")),
        parser(mandatory_whitespace),
        parser(parse_statement),
        parser(statement_terminator),
        parser(loop_body),
    ).map(
        |(_, _, head, _, body)| Statement::WhileStatement(box head, body)
    );

    let mut for_statement = (
        (
            try(string("for")),
            parser(mandatory_whitespace),
        ),
        ident(),
        (
            parser(mandatory_whitespace),
            try(string("in")),
            parser(mandatory_whitespace),
        ),
        many1(parser(parse_expression)),
        (parser(statement_terminator), parser(whitespace)),
        parser(loop_body),
    ).map(
        |(_, name, _, head, _, body)|
        Statement::ForStatement(name, head, body)
    );

    let mut function_definition = try(
        (
            ident(),
            (
                parser(whitespace),
                token('('),
                parser(whitespace),
                token(')'),
                parser(whitespace),
            ),
            parser(parse_statement),
        )
    ).map(|(name, _,  body)| Statement::FunctionDef(name, box body));

    let mut block = between(
        token('{'),
        token('}'),
        many1(
            (
                parser(parse_statement),
                parser(statement_terminator)
            ).map(|(stmt, _)| stmt)
        )
    ).map(|block| Statement::Block(block));

    choice([
        &mut block as RefParse<_, _>,
        &mut if_statement,
        &mut while_statement,
        &mut for_statement,
        &mut function_definition,
        &mut env_statement,
        &mut raw_func_call,
    ]).parse_stream(input)
}

fn parse_raw_string_char<R: Stream<Item=char>>(
    input: R
) -> ParseResult<char, R> {
    fn is_special(c: char) -> bool {
        c == '\\' ||
            c == '$'  ||
            c == '('  ||
            c == ')'  ||
            c == '{'  ||
            c == '}'  ||
            c == '"'  ||
            c == '\'' ||
            c == ' '  ||
            c == '*'  ||
            c == '?'  ||
            c == '|'  ||
            c == '&'  ||
            c == '#'  ||
            c == ';'
    }

    (
        try(not_followed_by(token('\n'))),
        choice(
            [
                &mut satisfy(|c| !is_special(c)) as RefParse<R, _>,
                &mut try(
                    (
                        token('\\'),
                        satisfy(is_special)
                    )
                ).map(|(_, b)| b),
                &mut try(
                    (
                        token('\\'),
                        not_followed_by(token('\n'))
                    )
                ).map(|(f, _)| f),
            ]
        )
    ).map(|(_, a)| a).parse_stream(input)
}

fn parse_one_expression_or_string<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    // HACK HACK HACK
    // If Dash didn't implement backticks my life would be much easier but I'll
    // put this technically-working hack in instead of ruining my fairly-clean
    // parsing logic.
    fn backtick_expansion<R: Stream<Item=char>>(
        input: R
    ) -> ParseResult<Expression, R> {
        let escaped_backtick = (token('\\'), token('`')).map(|_| '`');
        let escaped_backslash = (token('\\'), token('\\')).map(|_| '\\');
        let mut anything_else = none_of(iter::once('`'));

        between(
            token('`'),
            token('`'),
            optional(
                many1(
                    choice([
                        &mut try(escaped_backslash) as RefParse<_, _>,
                        // We `try` here since we want to allow backslashes to be
                        // interpolated literally if they don't have anything to escape.
                        // I'm pretty sure this is the POSIX/Dash behaviour.
                        &mut try(escaped_backtick),
                        &mut anything_else,
                    ])
                )
            )
        ).map(
            |maybe_backtick_string| {
                if let Some(backtick_string) = maybe_backtick_string {
                    Expression::Expand(
                        box Statement::FunctionCall(
                            vec![],
                            Expression::Literal("eval".into()),
                            vec![Expression::Literal(backtick_string)],
                        )
                    )
                } else {
                    // Yes, Dash's logic here really is this convoluted
                    Expression::Literal("".into())
                }
            }
        ).parse_stream(input)
    }

    choice(
        [
            &mut parser(backtick_expansion) as RefParse<_, _>,
            &mut between(
                token('"'),
                token('"'),
                parser(parse_double_string),
            ),
            &mut parser(parse_one_expression),
        ]
    ).parse_stream(input)
}

fn parse_expression<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    many1(
        parser(parse_one_expression_or_string)
    ).map(
        |all: Vec<_>|
        if all.len() == 1 {
            all.into_iter().next().unwrap()
        } else {
            Expression::Concat(all)
        }
    ).parse_stream(input)
}

// TODO: Roll *_char functions together
fn parse_double_string_char<R: Stream<Item=char>>(
    input: R
) -> ParseResult<char, R> {
    fn is_special(c: char) -> bool {
        c == '\\' ||
            c == '$'  ||
            c == '('  ||
            c == ')'  ||
            c == '['  ||
            c == ']'  ||
            c == '{'  ||
            c == '}'  ||
            c == '"'  ||
            c == '\'' ||
            c == '*'  ||
            c == '?'  ||
            c == '|'  ||
            c == '&'  ||
            c == '#'  ||
            c == ';'
    }

    choice(
        [
            &mut satisfy(|c| !is_special(c)) as RefParse<R, _>,
            &mut try(
                (
                    token('\\'),
                    satisfy(is_special)
                )
            ).map(|(_, b)| b),
            &mut token('\\'),
        ]
    ).parse_stream(input)
}

fn parse_double_string<R: Stream<Item=char>>(
    input: R,
) -> ParseResult<Expression, R> {
    parse_substitutable_string(
        input,
        parser(parse_one_expression)
            .map(Box::new)
            .map(Expression::Escape)
    ).map(
        |(opt, rest)|
        (opt.unwrap_or(Expression::Literal("".into())), rest)
    )
}

fn parse_variable_options<R: Stream<Item=char>>(
    input: R,
) -> ParseResult<Option<Expression>, R> {
    parse_substitutable_string(
        input,
        parser(parse_one_expression_or_string),
    )
}

fn parse_substitutable_string<
    R: Stream<Item=char>,
    E: Parser<Input=R, Output=Expression>
>(
    input: R, expression_parser: E,
) -> ParseResult<Option<Expression>, R> {
    many1(
        choice(
            [
                &mut try(
                    many1(
                        choice([
                            &mut parser(parse_double_string_char) as RefParse<_, _>,
                            &mut satisfy(char::is_whitespace),
                        ])
                    )
                ).map(Expression::Literal) as RefParse<_, _>,
                &mut try(expression_parser),
            ]
        )
    ).map(
        |all: Vec<_>|
        if all.len() == 0 {
            Expression::Literal("".into())
        } else if all.len() == 1 {
            all.into_iter().next().unwrap()
        } else {
            Expression::Concat(all)
        }
    ).map(
        Some
    ).or(
        value(None)
    ).parse_stream(
        input
    )
}

fn is_ident(c: char) -> bool {
    (c >= 'a' && c <= 'z') ||
        (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9') ||
        (c == '_') ||
        (c == '[') ||
        (c == ']')
}

fn is_ident_start(c: char) -> bool {
    (c >= 'a' && c <= 'z') ||
        (c >= 'A' && c <= 'Z') ||
        (c == '_') ||
        (c == '[') ||
        (c == ']')
}

fn ident<R: Stream<Item=char>>() -> impl Parser<Input=R, Output=String> {
    (satisfy(is_ident_start), many(satisfy(is_ident))).map(
        |(left, rest): (char, String)| format!("{}{}", left, rest)
    )
}

fn parse_variable_reference<R: Stream<Item=char>>(
    input: R
) -> ParseResult<VariableReference, R> {
    choice(
        [
            // `try` is fine here since we only need 1 char lookahead
            &mut try(
                (
                    token('_'),
                    not_followed_by(satisfy(is_ident)),
                )
            ).map(
                |_| VariableReference::Magic(MagicVar::LastLastArgument)
            ) as RefParse<_, _>,
            &mut ident().map(String::into),
            &mut choice([
                &mut token('0').map(|_| MagicVar::ScriptName)
                    as RefParse<_, _>,
                &mut token('#').map(|_| MagicVar::NumArgs),
                &mut token('@').map(|_| MagicVar::Arguments),
                &mut token('*').map(|_| MagicVar::ArgumentString),
                &mut token('?').map(|_| MagicVar::LastExitCode),
                &mut token('!').map(|_| MagicVar::LastProcId),
                &mut token('$').map(|_| MagicVar::ProcId),
                &mut token('-').map(|_| MagicVar::ShellArgs),
                &mut many1(digit())
                    .and_then(|d: String| d.parse().map(MagicVar::Argument)),
            ]).map(VariableReference::Magic)
        ]
    ).parse_stream(input)
}


fn parse_bracketed_var<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    // I hate using this `also_null` hack, but it's the cleanest way I can do
    // this. In my defense, the standardised behaviour is a hack too.
    fn make_and_then(
        also_null: bool,
        exp: Option<Rc<Expression>>,
    ) -> LookupBehavior {
        let behaviour = VariableBehavior::Substitute(
            exp.unwrap_or(
                Rc::new(Expression::Literal("".into()))
            )
        );

        let null_behaviour = if also_null {
            VariableBehavior::Inherit
        } else {
            behaviour.clone()
        };

        LookupBehavior {
            if_set: behaviour,
            if_null: null_behaviour,
            if_unset: VariableBehavior::Inherit,
        }
    }

    fn make_default(
        also_null: bool,
        exp: Option<Rc<Expression>>,
    ) -> LookupBehavior {
        let behaviour = VariableBehavior::Substitute(
            exp.unwrap_or(
                Rc::new(Expression::Literal("".into()))
            )
        );

        LookupBehavior {
            if_set: VariableBehavior::Inherit,
            if_null: if also_null {
                behaviour.clone()
            } else {
                VariableBehavior::Inherit
            },
            if_unset: behaviour,
        }
    }

    fn make_assign(
        also_null: bool,
        exp: Option<Rc<Expression>>,
    ) -> LookupBehavior {
        let behaviour = VariableBehavior::Assign(
            exp.unwrap_or(
                Rc::new(Expression::Literal("".into()))
            )
        );

        LookupBehavior {
            if_set: VariableBehavior::Inherit,
            if_null: if also_null {
                behaviour.clone()
            } else {
                VariableBehavior::Inherit
            },
            if_unset: behaviour,
        }
    }

    fn make_fail(
        also_null: bool,
        exp: Option<Rc<Expression>>,
    ) -> LookupBehavior {
        let behaviour = VariableBehavior::Fail(exp);

        LookupBehavior {
            if_set: VariableBehavior::Inherit,
            if_null: if also_null {
                behaviour.clone()
            } else {
                VariableBehavior::Inherit
            },
            if_unset: behaviour,
        }
    }

    between(
        token('{'),
        token('}'),
        (
            parser(parse_variable_reference),
            optional(
                (
                    optional(token(':').map(|_: char| ())),
                    choice(
                        [
                            &mut token('-').map(
                                |_| make_default as
                                    fn(bool, Option<Rc<Expression>>) ->
                                    LookupBehavior
                            ) as RefParse<R, _>,
                            &mut token('=').map(
                                |_| make_assign as _
                            ),
                            &mut token('?').map(
                                |_| make_fail as _
                            ),
                            &mut token('+').map(
                                |_| make_and_then as _
                            ),
                        ]
                    ),
                    parser(parse_variable_options),
                ).map(
                    |(
                        maybe_colon,
                        make_fn,
                        exp
                    ): (
                        Option<()>,
                        fn(bool, Option<Rc<Expression>>) ->
                            LookupBehavior,
                        Option<Expression>,
                    )| ->
                        LookupBehavior
                    {
                        make_fn(
                            maybe_colon.is_some(),
                            exp.map(Rc::new),
                        )
                    }
                ),
            )
        )
    ).map(
        |(name, behaviour): (
            VariableReference, Option<LookupBehavior>
        )|
        Expression::VariableReference(
            name,
            behaviour.unwrap_or_default(),
        )
    ).parse_stream(input)
}

fn parse_one_expression<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    let mut star_tok = token('*').map(|_| Glob::Many);
    let mut qust_tok = token('?').map(|_| Glob::One);
    let glob = choice(
        [
            &mut star_tok as RefParse<R, _>,
            &mut qust_tok,
        ]
    );

    let single_string = parser(single_string);

    let expansion = (
        token('$'),
        between(
            token('('),
            token(')'),
            parser(parse_statement),
        )
    ).map(|(_, second)| second);

    let mut var_ref = parser(parse_variable_reference)
        .map(
            |s|
            Expression::VariableReference(
                s,
                Default::default(),
            )
        );
    let mut bracketed_var_ref = parser(parse_bracketed_var);

    let mut variable = (
        token('$'),
        choice(
            [
                // TODO: Have seperate datatypes representing the special vars
                //       compared to "regular" vars.
                &mut var_ref as RefParse<R, _>,
                &mut bracketed_var_ref,
            ]
        )
    ).map(|(_, second)| second);

    let raw_string = many1(parser(parse_raw_string_char));

    choice(
        [
            &mut try(expansion)
                .map(Box::new)
                .map(Expression::Expand)
                as RefParse<R, _>,
            &mut variable,
            &mut single_string.map(Expression::Literal),
            &mut glob.map(Expression::Glob),
            &mut raw_string.map(Expression::Literal),
        ]
    ).parse_stream(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn just_string() {
        assert_eq!(
            parse_expression("'One two \\'three four\\' five six'").unwrap().0,
            Expression::Literal(
                "One two 'three four' five six".into()
            )
        );
    }

    #[test]
    fn just_var() {
        assert_eq!(
            parse_expression("$test").unwrap().0,
            Expression::VariableReference(
                "test".into(),
                Default::default(),
            )
        );
    }

    #[test]
    fn braced_var() {
        assert_eq!(
            parse_expression("${test}").unwrap().0,
            Expression::VariableReference(
                "test".into(),
                Default::default(),
            )
        );
    }

    #[test]
    fn raw_string() {
        assert_eq!(
            parse_expression(
                "One\\ Two\\$Three"
            ).unwrap().0,
            Expression::Literal(
                "One Two$Three".into()
            )
        );
    }

    #[test]
    fn double_string() {
        assert_eq!(
            parse_expression(
                "\"$test\"\"One\\ $test Two\\$Three\""
            ).unwrap().0,
            Expression::Concat(
                vec![
                    Expression::Escape(
                        box Expression::VariableReference(
                            "test".into(),
                            Default::default(),
                        )
                    ),
                    Expression::Concat(
                        vec![
                            Expression::Literal("One\\ ".into()),
                            Expression::Escape(
                                box Expression::VariableReference(
                                    "test".into(),
                                    Default::default(),
                                )
                            ),
                            Expression::Literal(" Two$Three".into()),
                        ]
                    ),
                ]
            )
        );
    }

    #[test]
    fn glob() {
        assert_eq!(
            parse_expression(
                "*"
            ).unwrap().0,
            Expression::Glob(Glob::Many)
        );
        assert_eq!(
            parse_expression(
                "?"
            ).unwrap().0,
            Expression::Glob(Glob::One)
        );
    }

    #[test]
    fn concat() {
        assert_eq!(
            parse_expression(
                "'The value of $test is '$test' and txt files starting with \
                 $x_0 and ending with $y_1 are '${x_0}*${y_1}?txt"
            ).unwrap().0,
            Expression::Concat(
                vec![
                    Expression::Literal(
                        "The value of $test is ".into()
                    ),
                    Expression::VariableReference(
                        "test".into(),
                        Default::default(),
                    ),
                    Expression::Literal(
                        " and txt files starting with $x_0 and ending with \
                         $y_1 are ".into()
                    ),
                    Expression::VariableReference(
                        "x_0".into(),
                        Default::default(),
                    ),
                    Expression::Glob(Glob::Many),
                    Expression::VariableReference(
                        "y_1".into(),
                        Default::default(),
                    ),
                    Expression::Glob(Glob::One),
                    Expression::Literal("txt".into()),
                ]
            )
        );
    }

    #[test]
    fn statement() {
        assert_eq!(
            parse_statement(
                "ls -clt $PWD \n"
            ).unwrap().0,
            Statement::FunctionCall(
                vec![],
                Expression::Literal("ls".into()),
                vec![
                    Expression::Literal(
                        "-clt".into()
                    ),
                    Expression::VariableReference(
                        "PWD".into(),
                        Default::default(),
                    ),
                ]
            )
        );
    }

    #[test]
    fn comments() {
        assert_eq!(
            parse_statement(
                "ls -clt $PWD # Hello, world! \n"
            ).unwrap().0,
            Statement::FunctionCall(
                vec![],
                Expression::Literal("ls".into()),
                vec![
                    Expression::Literal(
                        "-clt".into()
                    ),
                    Expression::VariableReference(
                        "PWD".into(),
                        Default::default(),
                    ),
                ]
            )
        );
    }

    #[test]
    fn literal_newline() {
        assert_eq!(
            parse_statement(
                "ls -clt \\\n   $PWD;"
            ).unwrap().0,
            Statement::FunctionCall(
                vec![],
                Expression::Literal("ls".into()),
                vec![
                    Expression::Literal(
                        "-clt".into()
                    ),
                    Expression::VariableReference(
                        "PWD".into(),
                        Default::default(),
                    ),
                ]
            )
        );
    }

    #[test]
    fn parse_url() {
        let out = parse_expression("$(curl http://example.com)");

        assert_eq!(
            out.unwrap().0,
            Expression::Expand(
                box Statement::FunctionCall(
                    vec![],
                    Expression::Literal("curl".into()),
                    vec![Expression::Literal("http://example.com".into())],
                )
            )
        );
    }

    #[test]
    fn lookup_behaviours() {
        let out = parse_statement("${CC:-gcc} -S ${VERBOSE:+-v} ${file?}");
        let cc_behaviour = VariableBehavior::Substitute(
            Rc::new(Expression::Literal("gcc".into()))
        );

        assert_eq!(
            out.unwrap().0,
            Statement::FunctionCall(
                vec![],
                Expression::VariableReference(
                    "CC".into(),
                    LookupBehavior {
                        if_null: cc_behaviour.clone(),
                        if_unset: cc_behaviour.clone(),
                        if_set: Default::default(),
                    }
                ),
                vec![
                    Expression::Literal("-S".into()),
                    Expression::VariableReference(
                        "VERBOSE".into(),
                        LookupBehavior {
                            if_set: VariableBehavior::Substitute(
                                Rc::new(Expression::Literal("-v".into()))
                            ),
                            .. Default::default()
                        }
                    ),
                    Expression::VariableReference(
                        "file".into(),
                        LookupBehavior {
                            if_unset: VariableBehavior::Fail(None),
                            .. Default::default()
                        }
                    ),
                ],
            )
        );
    }

    #[test]
    fn magic_args() {
        fn make_var(magic: MagicVar) -> Expression {
            Expression::VariableReference(
                VariableReference::Magic(
                    magic,
                ),
                Default::default(),
            )
        }

        let out = parse_expression(
            "${@}$#$1234test$123test$1test$0test$-$!$?$_$_123$_hello_"
        );

        let left = out.unwrap().0;
        let right = Expression::Concat(
            vec![
                make_var(MagicVar::Arguments),
                make_var(MagicVar::NumArgs),
                make_var(MagicVar::Argument(1234)),
                Expression::Literal("test".into()),
                make_var(MagicVar::Argument(123)),
                Expression::Literal("test".into()),
                make_var(MagicVar::Argument(1)),
                Expression::Literal("test".into()),
                make_var(MagicVar::ScriptName),
                Expression::Literal("test".into()),
                make_var(MagicVar::ShellArgs),
                make_var(MagicVar::LastProcId),
                make_var(MagicVar::LastExitCode),
                make_var(MagicVar::LastLastArgument),
                Expression::VariableReference(
                    VariableReference::Ref("_123".into()),
                    Default::default(),
                ),
                Expression::VariableReference(
                    VariableReference::Ref("_hello_".into()),
                    Default::default(),
                ),
            ]
        );
        {
            match (&left, &right) {
                (left_val, right_val) => {
                    if !(
                        (*left_val == *right_val) &&
                            (*right_val == *left_val)
                    ) {
                        panic!(
                            "assertion failed: `(left == right) && (right == \
                             left)` (left: `{:#?}`, right: `{:#?}`)",
                            *left_val,
                            *right_val
                        )
                    }
                }
            }
        }
    }

    #[test]
    fn expression_no_whitespace_at_end() {
        let out = parse_expression("test");

        assert!(out.unwrap().1.into_inner().is_empty());
    }

    #[test]
    fn command_substitution() {
        let out = parse_statement("echo $(echo ${test})");

        assert_eq!(
            out.unwrap().0,
            Statement::FunctionCall(
                vec![],
                Expression::Literal("echo".into()),
                vec![
                    Expression::Expand(
                        box Statement::FunctionCall(
                            vec![],
                            Expression::Literal(
                                "echo".into()
                            ),
                            vec![
                                Expression::VariableReference(
                                    "test".into(),
                                    Default::default(),
                                )
                            ]
                        )
                    ),
                ]
            )
        )
    }

    #[test]
    fn set_vars() {
        let out = parse_statement("first=1 second=$first");

        assert_eq!(
            out.unwrap().0,
            Statement::SetParameters(
                vec![
                    (
                        "first".into(),
                        Expression::Literal("1".into()),
                    ),
                    (
                        "second".into(),
                        Expression::VariableReference(
                            "first".into(),
                            Default::default(),
                        ),
                    )
                ]
            )
        )
    }

    #[test]
    fn statement_term() {
        let out = parser(statement_terminator).parse_stream(
            "    ;     "
        );
        out.unwrap();
    }

    #[test]
    fn statement_term_nl() {
        let out = parser(statement_terminator).parse_stream(
            "    \n     "
        );
        out.unwrap();
    }

    #[test]
    fn run_with_vars() {
        let out = parse_statement("first=1 second=$first do_thing one two");

        assert_eq!(
            out.unwrap().0,
            Statement::FunctionCall(
                vec![
                    (
                        "first".into(),
                        Expression::Literal("1".into())
                    ),
                    (
                        "second".into(),
                        Expression::VariableReference(
                            "first".into(),
                            Default::default(),
                        )
                    ),
                ],
                Expression::Literal("do_thing".into()),
                vec![
                    Expression::Literal("one".into()),
                    Expression::Literal("two".into()),
                ]
            )
        )
    }

    #[test]
    fn if_statement() {
        let out = parse_statement("if test 1 -le 2; then; echo test; fi");

        assert_eq!(
            out.unwrap().0,
            Statement::IfStatement(
                box Statement::FunctionCall(
                    vec![],
                    Expression::Literal("test".into()),
                    vec![
                        Expression::Literal("1".into()),
                        Expression::Literal("-le".into()),
                        Expression::Literal("2".into()),
                    ]
                ),
                vec![
                    Statement::FunctionCall(
                        vec![],
                        Expression::Literal("echo".into()),
                        vec![
                            Expression::Literal("test".into()),
                        ]
                    ),
                ]
            )
        )
    }

    #[test]
    fn multiline_if() {
        let out = parse_statement(
            r#"if [ 1 -le 2 ]; then
                echo test
              fi
"#);

        assert_eq!(
            out.unwrap().0,
            Statement::IfStatement(
                box Statement::FunctionCall(
                    vec![],
                    Expression::Literal("[".into()),
                    vec![
                        Expression::Literal("1".into()),
                        Expression::Literal("-le".into()),
                        Expression::Literal("2".into()),
                        Expression::Literal("]".into()),
                    ]
                ),
                vec![
                    Statement::FunctionCall(
                        vec![],
                        Expression::Literal("echo".into()),
                        vec![
                            Expression::Literal("test".into()),
                        ]
                    ),
                ]
            )
        )
    }

    #[test]
    fn test_command() {
        let out = parse_statement("[ 1 -le 2 ]");

        assert_eq!(
            out.unwrap().0,
            Statement::FunctionCall(
                vec![],
                Expression::Literal("[".into()),
                vec![
                    Expression::Literal("1".into()),
                    Expression::Literal("-le".into()),
                    Expression::Literal("2".into()),
                    Expression::Literal("]".into()),
                ]
            )
        )
    }

    #[test]
    fn while_loop() {
        let out = parse_statement("while test 1 -le 2; do echo test; done");

        assert_eq!(
            out.unwrap().0,
            Statement::WhileStatement(
                box Statement::FunctionCall(
                    vec![],
                    Expression::Literal("test".into()),
                    vec![
                        Expression::Literal("1".into()),
                        Expression::Literal("-le".into()),
                        Expression::Literal("2".into()),
                    ]
                ),
                vec![
                    Statement::FunctionCall(
                        vec![],
                        Expression::Literal("echo".into()),
                        vec![
                            Expression::Literal("test".into()),
                        ]
                    ),
                ]
            )
        )
    }

    #[test]
    fn backticks() {
        let out = parse_expression("`pwd`/first-file");

        assert_eq!(
            out.unwrap().0,
            Expression::Concat(
                vec![
                    Expression::Expand(
                        box Statement::FunctionCall(
                            vec![],
                            Expression::Literal("eval".into()),
                            vec![
                                Expression::Literal("pwd".into()),
                            ],
                        )
                    ),
                    Expression::Literal("/first-file".into()),
                ]
            )
        )
    }
}
