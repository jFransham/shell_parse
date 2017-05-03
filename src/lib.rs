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
#[derive(Debug, PartialEq)]
pub struct FunctionDef(Vec<Statement>);

#[derive(Debug, PartialEq)]
pub enum Statement {
    FunctionDef {
        name: String,
        body: FunctionDef,
    },
    FunctionCall(Expression, Vec<Expression>),
}

#[derive(Debug, PartialEq)]
pub enum Glob {
    Many,
    One,
}

#[derive(Debug, PartialEq, Default)]
pub struct LookupBehavior {
    if_set:   VariableBehavior,
    if_null:  VariableBehavior,
    if_unset: VariableBehavior,
}

#[derive(Clone, Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub enum Expression {
    Literal(String),
    Glob(Glob),
    Concat(Vec<Expression>),
    // Ideally convert this to use Rc<str> so we can do simple reference
    // equality
    VariableReference(String, LookupBehavior),
    Escape(Box<Expression>)
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
) -> impl Iterator<Item=Statement> {
    struct StatementStream<T>(Option<T>);

    impl<T: Stream<Item=char>> Iterator for StatementStream<T> {
        type Item = Statement;

        fn next(&mut self) -> Option<Statement> {
            let opt = self.0.take();

            if let Some(to_parse) = opt {
                let parsed = parse_statement(to_parse);

                if let Ok((out, rest)) = parsed {
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
    let whitespace = optional(parser(mandatory_whitespace));

    (
        whitespace,
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
        skip_many1(parser(statement_terminator)),
    ).map(
        |(_, s, _)| s
    ).parse_stream(input)
}

// TODO: Escaped newlines are counted as whitespace instead of as nothing
pub fn parse_expression<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    fn is_ident(c: char) -> bool {
        (c >= 'a' && c <= 'z') ||
        (c >= 'A' && c <= 'Z') ||
        (c >= '0' && c <= '9') ||
        (c == '_')
    }

    fn is_special(c: char) -> bool {
        c == '\\' ||
        c == '$'  ||
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

    let variable_reference = (
        token('$'),
        choice(
            [
                // TODO: Have seperate datatypes representing the special vars
                //       compared to "regular" vars.
                box many1(satisfy(is_ident))
                    .map(|s| (s, None)) as BoxParse<R, _>,
                box between(
                    token('{'),
                    token('}'),
                    (
                        many1(satisfy(is_ident)),
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
                                optional(try(parser(parse_expression))),
                            ).map(
                                |(
                                    maybe_colon,
                                    make_fn,
                                    maybe_exp
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
                                        maybe_exp.map(Rc::new),
                                    )
                                }
                            ),
                        )
                    )
                ),
            ]
        )
    ).map(
        |(_, (name, behaviour)): (_, (String, Option<LookupBehavior>))|
        Expression::VariableReference(
            name,
            behaviour.unwrap_or_default(),
        )
    );

    let raw_string = many1(
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
        ).map(|(_, a)| a)
    );

    let mut expression = many1(
        choice(
            [
                box variable_reference as BoxParse<R, _>,
                box single_string.map(Expression::Literal),
                box glob.map(Expression::Glob),
                box raw_string.map(Expression::Literal),
            ]
        )
    ).map(
        |all: Vec<_>|
        if all.len() == 1 {
            all.into_iter().next().unwrap()
        } else {
            Expression::Concat(all)
        }
    );

    expression.parse_stream(input)
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
                "   ls -clt\\\n   $PWD;"
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
        let out = parse_statement("${CC:-gcc} -S ${VERBOSE:+-v} ${file?};");
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

    // TODO: Can't parse the `curl` statement
    #[test]
    fn everything() {
        let out = parse_statements(
            "
#!/bin/sh

. /lib/functions/keezel.sh

# TODO: Extract this to config

set -e
/etc/scripts/generate-logs.sh $LOG
tar -cf $LOG_COMPLETE $LOG
set +e

curl \
  -A ${USER_AGENT} \
  -X POST \
  --data-binary @${LOG_COMPLETE:-/var/log/keezel/log.gz} \
  --header 'Content-Type:application/octet-stream' \
  --output ${LOG_COMPLETE-/tmp/keezel.tar}.json.out \
  ${SERVER_URL:?No server URL found for user agent ${USER_AGENT}}

if grep -q '\"code\":200' ${LOG_COMPLETE}.json.out; then
  notice 'Log upload successful'
  awk -F, '{print substr($1,index($1, \":\")+1)}' ${LOG_COMPLETE}.json.out | \
                                         sed 's/\\\"//g'
  rm ${LOG_COMPLETE:+.}*
  exit 0
fi

alert 'Log upload failed'
exit 1
            "
        );

        panic!("{:?}", out.collect::<Vec<_>>());
    }
}
