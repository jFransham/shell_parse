#![feature(box_syntax)]
#![feature(conservative_impl_trait)]

extern crate combine;

use combine::*;
use combine::char::*;
use std::iter;
use std::rc::Rc;

// TODO: Just store string slice and lazily create function? Probably not worth
//       it, unused functions are rare and users can just use `shellcheck` to
//       lint against it.
#[derive(Debug, Clone, PartialEq)]
pub struct FunctionDef(Vec<Statement>);

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    FunctionDef {
        name: String,
        body: FunctionDef,
    },
    FunctionCall(Expression, Vec<Expression>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Glob {
    Many,
    One,
}

#[derive(Debug, Clone, PartialEq)]
pub enum VariableReference {
    Magic(MagicVar),
    Ref(String),
}

impl<T: Into<String>> From<T> for VariableReference {
    fn from(other: T) -> Self {
        VariableReference::Ref(other.into())
    }
}

// $* is equal to `Escaped(Arguments)`
// "$*" is equal to `Escaped(Escaped(Arguments))` (this is the only method of
// getting a nested Escaped in the AST)
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
    // $N: Starts from 1 in the script, but 0 internally.
    //     This is because $0 is considered a "special parameter".
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
    VariableReference(VariableReference, LookupBehavior),
    Expand(Box<Statement>),
    Escape(Box<Expression>),
}

type BoxParse<'a, T, O> = Box<Parser<Input=T, Output=O> + 'a>;

fn single_string<R: Stream<Item=char>>(input: R) -> ParseResult<String, R> {
    let single_string_char = choice(
        [
            box try(string("\\'")).map(|_| '\'') as BoxParse<R, _>,
            box none_of(iter::once('\'')) as BoxParse<R, _>,
        ]
    );

    between(
        token('\''),
        token('\''),
        many(single_string_char)
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
    input: R,
) -> ParseResult<(), R> {
    try(
        (
            optional(parser(mandatory_whitespace)),
            choice(
                [
                    box parser(comment_or_newline) as BoxParse<_, _>,
                    box token(';').map(|_| ()),
                ]
            ),
        )
    ).map(|_| ()).parse_stream(input)
}

pub fn parse_statements<R: Stream<Item=char>>(
    input: R,
) -> impl Iterator<Item=Statement>

{
    struct StatementStream<T>(Option<T>);

    impl<T: Stream<Item=char>> Iterator for StatementStream<T> {
        type Item = Statement;

        fn next(&mut self) -> Option<Statement> {
            let opt = self.0.take();

            if let Some(to_parse) = opt {
                let parsed = (
                    parser(parse_statement),
                    skip_many1(parser(statement_terminator)),
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
        skip_many(parser(statement_terminator)).parse_stream(input);

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

fn mandatory_whitespace<R: Stream<Item=char>>(
    input: R
) -> ParseResult<(), R> {
    skip_many1(
        choice(
            [
                box skip_many1(
                    satisfy(is_whitespace_char)
                ) as BoxParse<R, _>,
                box skip_many1(
                    parser(escaped_newline)
                ) as BoxParse<R, _>,
            ]
        )
    ).parse_stream(input)
}

pub fn parse_statement<R: Stream<Item=char>>(
    input: R,
) -> ParseResult<Statement, R> {
    let whitespace1 = optional(parser(mandatory_whitespace));
    let whitespace2 = optional(parser(mandatory_whitespace));

    (
        whitespace1,
        (
            parser(parse_expression),
            many(
                try(
                    (
                        // TODO: We waste time re-parsing whitespace here after
                        //       the last expression, since the
                        //       `parse_expression` will fail and then the
                        //       whitespace will get rolled back. This is only
                        //       an issue for EOL whitespace and line
                        //       continuations, so it's not so bad, but we can
                        //       do better.
                        //
                        //       Maybe switch the order of these two statements?
                        parser(mandatory_whitespace),
                        parser(parse_expression)
                    )
                ).map(|(_, exp)| exp)
            ),
        ).map(|(name, args)| Statement::FunctionCall(name, args)),
        whitespace2,
    ).map(
        |(_, s, _)| s
    ).parse_stream(input)
}
pub fn parse_raw_string_char<R: Stream<Item=char>>(
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
                box satisfy(|c| !is_special(c)) as BoxParse<R, _>,
                box try(
                    (
                        token('\\'),
                        satisfy(is_special)
                    )
                ).map(|(_, b)| b),
                box try(
                    (
                        token('\\'),
                        not_followed_by(token('\n'))
                    )
                ).map(|(f, _)| f),
            ]
        )
    ).map(|(_, a)| a).parse_stream(input)
}

pub fn parse_variable_options_char<R: Stream<Item=char>>(
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
            box satisfy(|c| !is_special(c)) as BoxParse<R, _>,
            box try(
                (
                    token('\\'),
                    satisfy(is_special)
                )
            ).map(|(_, b)| b),
            box token('\\'),
        ]
    ).parse_stream(input)
}

pub fn parse_one_expression_or_double_string<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    choice(
        [
            box parser(parse_one_expression) as BoxParse<_, _>,
            box between(
                token('"'),
                token('"'),
                parser(parse_double_string),
            ),
        ]
    ).parse_stream(input)
}

pub fn parse_expression<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    many1(
        parser(parse_one_expression_or_double_string)
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
pub fn parse_double_string_char<R: Stream<Item=char>>(
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
            box satisfy(|c| !is_special(c)) as BoxParse<R, _>,
            box try(
                (
                    token('\\'),
                    satisfy(is_special)
                )
            ).map(|(_, b)| b),
            box token('\\'),
        ]
    ).parse_stream(input)
}

pub fn parse_double_string<R: Stream<Item=char>>(
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

pub fn parse_variable_options<R: Stream<Item=char>>(
    input: R,
) -> ParseResult<Option<Expression>, R> {
    parse_substitutable_string(
        input,
        parser(parse_one_expression_or_double_string),
    )
}

pub fn parse_substitutable_string<
    R: Stream<Item=char>,
    E: Parser<Input=R, Output=Expression>
>(
    input: R, expression_parser: E,
) -> ParseResult<Option<Expression>, R> {
    many1(
        choice(
            [
                box try(
                    many1(
                        choice([
                            box parser(parse_double_string_char) as BoxParse<_, _>,
                            box satisfy(char::is_whitespace),
                        ])
                    )
                ).map(Expression::Literal) as BoxParse<_, _>,
                box try(expression_parser),
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

pub fn parse_one_expression<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    fn is_ident(c: char) -> bool {
        (c >= 'a' && c <= 'z') ||
        (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9') ||
        (c == '_')
    }

    fn is_ident_start(c: char) -> bool {
        (c >= 'a' && c <= 'z') ||
            (c >= 'A' && c <= 'Z') ||
            (c == '_')
    }

    fn ident<R: Stream<Item=char>>(input: R) -> ParseResult<String, R> {
        (satisfy(is_ident_start), many(satisfy(is_ident))).map(
            |(left, rest): (char, String)| format!("{}{}", left, rest)
        ).parse_stream(input)
    }

    fn variable_reference<R: Stream<Item=char>>(
        input: R
    ) -> ParseResult<VariableReference, R> {
        choice(
            [
                // `try` is fine here since we only need 1 char lookahead
                box try(
                    (
                        token('_'),
                        not_followed_by(satisfy(is_ident)),
                    )
                ).map(
                    |_| VariableReference::Magic(MagicVar::LastLastArgument)
                ) as BoxParse<_, _>,
                box parser(ident).map(String::into),
                box choice([
                    box token('0').map(|_| MagicVar::ScriptName)
                        as BoxParse<_, _>,
                    box token('#').map(|_| MagicVar::NumArgs),
                    box token('@').map(|_| MagicVar::Arguments),
                    box token('?').map(|_| MagicVar::LastExitCode),
                    box token('!').map(|_| MagicVar::LastProcId),
                    box token('$').map(|_| MagicVar::ProcId),
                    box token('-').map(|_| MagicVar::ShellArgs),
                    box many1(digit())
                        .and_then(|d: String| d.parse().map(MagicVar::Argument)),
                ]).map(VariableReference::Magic)
            ]
        ).parse_stream(input)
    }

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

    let glob = choice(
        [
            box token('*').map(|_| Glob::Many) as BoxParse<R, _>,
            box token('?').map(|_| Glob::One) as BoxParse<R, _>,
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

    let variable = (
        token('$'),
        choice(
            [
                // TODO: Have seperate datatypes representing the special vars
                //       compared to "regular" vars.
                box parser(variable_reference)
                    .map(
                        |s|
                        Expression::VariableReference(
                            s,
                            Default::default(),
                        )
                    ) as BoxParse<R, _>,
                box between(
                    token('{'),
                    token('}'),
                    (
                        parser(variable_reference),
                        optional(
                            (
                                optional(token(':').map(|_: char| ())),
                                choice(
                                    [
                                        box token('-').map(
                                            |_| make_default as
                                                fn(bool, Option<Rc<Expression>>) ->
                                                    LookupBehavior
                                        ) as BoxParse<R, _>,
                                        box token('=').map(
                                            |_| make_assign as _
                                        ),
                                        box token('?').map(
                                            |_| make_fail as _
                                        ),
                                        box token('+').map(
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
                ),
            ]
        )
    ).map(|(_, second)| second);

    let raw_string = many1(parser(parse_raw_string_char));

    choice(
        [
            box try(expansion)
                .map(Box::new)
                .map(Expression::Expand)
                as BoxParse<R, _>,
            box variable,
            box single_string.map(Expression::Literal),
            box glob.map(Expression::Glob),
            box raw_string.map(Expression::Literal),
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
                "   ls -clt $PWD \n"
            ).unwrap().0,
            Statement::FunctionCall(
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
                "   ls -clt $PWD # Hello, world! \n"
            ).unwrap().0,
            Statement::FunctionCall(
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
                "   ls -clt \\\n   $PWD;"
            ).unwrap().0,
            Statement::FunctionCall(
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
    fn lookup_behaviours() {
        let out = parse_statement("${CC:-gcc} -S ${VERBOSE:+-v} ${file?}");
        let cc_behaviour = VariableBehavior::Substitute(
            Rc::new(Expression::Literal("gcc".into()))
        );

        assert_eq!(
            out.unwrap().0,
            Statement::FunctionCall(
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
    fn command_substitution() {
        let out = parse_statement("echo $(echo ${test})");

        assert_eq!(
            out.unwrap().0,
            Statement::FunctionCall(
                Expression::Literal("echo".into()),
                vec![
                    Expression::Expand(
                        box Statement::FunctionCall(
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

    // TODO: Can't parse the `curl` statement
    #[test]
    fn everything() {
        use std::fs::File;
        use std::io::Read;

        let mut file = File::open("test.sh").unwrap();
        let mut script = String::new();
        file.read_to_string(&mut script).unwrap();

        panic!(
            "{:#?}",
            parse_statements(
                &script as &str
            ).collect::<Vec<_>>()
        );
    }
}
