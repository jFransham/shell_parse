#![feature(box_syntax)]
#![feature(conservative_impl_trait)]

extern crate combine;

use combine::*;
use combine::char::*;
use std::iter;

// NOTE: We can't zero-copy parse because of character escaping. Damn it! It's
//       almost certainly possible to use some vector of an enum that can be
//       either an &str or an escaped char (or even just Vec<Cow<str>>) but it's
//       probably not worth it. The performance wins would just be from less
//       copying since the cache non-locality would cancel out any performance
//       from nixing allocation.

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
    FunctionCall {
        name: String, 
        arguments: Vec<Expression>,
    }
}

#[derive(Debug, PartialEq)]
pub enum Literal {
    String(String),
}

#[derive(Debug, PartialEq)]
pub enum Glob {
    Many,
    One,
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    Literal(Literal),
    Glob(Glob),
    Concat(Vec<Expression>),
    // Ideally convert this to use Rc<str> so we can do simple reference
    // equality
    VariableReference(String),
    Escape(Box<Expression>)
}

type BoxParse<'a, T, O> = Box<Parser<Input=T, Output=O> + 'a>;

fn single_string<R: Stream<Item=char>>(input: R) -> ParseResult<Literal, R> {
    let single_string_char = choice(
        [
            box try(string("\\'")).map(|_| '\'') as BoxParse<R, _>,
            box none_of(iter::once('\'')) as BoxParse<R, _>,
        ]
    );

    between(
        token('\''),
        token('\''),
        many(single_string_char).map(|chrs: String| chrs),
    ).map(
        Literal::String
    ).parse_stream(input)
}

pub fn parse_expression<R: Stream<Item=char>>(
    input: R
) -> ParseResult<Expression, R> {
    fn is_ident(c: char) -> bool {
        ((c >= 'a') & (c <= 'z')) |
        ((c >= 'A') & (c <= 'Z')) |
        ((c >= '0') & (c <= '9')) |
        (c == '_')
    }

    let glob = choice(
        [
            box token('*').map(|_| Glob::Many) as BoxParse<R, _>,
            box token('?').map(|_| Glob::One) as BoxParse<R, _>,
        ]
    );

    // let comment_or_newline =
    //     (
    //         optional(
    //             (
    //                 token('#'),
    //                 many(none_of(iter::once('\n'))),
    //             )
    //         ),
    //         token('\n'),
    //     );

    let single_string = parser(single_string);

    let unbraced_identifier = many1(satisfy(is_ident));

    let variable_reference = (
        token('$'),
        choice(
            [
                unbraced_identifier
            ]
        )
    ).map(|(_, b): (_, String)| b);

    let unescaped_in_raw_string = is_ident;

    let raw_string = many1(
        choice(
            [
                box satisfy(unescaped_in_raw_string) as BoxParse<R, _>,
                box try(
                    (
                        token('\\'),
                        satisfy(|c| !unescaped_in_raw_string(c))
                    ).map(|(_, b)| b)
                ) as BoxParse<R, _>,
                box token('\\'),
            ]
        )
    ).map(Literal::String);

    let mut expression = many1(
        choice(
            [
                box variable_reference.map(
                    Expression::VariableReference
                ) as BoxParse<R, _>,
                box single_string.map(Expression::Literal) as BoxParse<R, _>,
                box glob.map(Expression::Glob) as BoxParse<R, _>,
                box raw_string.map(Expression::Literal) as BoxParse<R, _>,
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
                Literal::String(
                    "One two 'three four' five six".into()
                )
            )
        );
    }

    #[test]
    fn just_var() {
        assert_eq!(
            parse_expression("$test").unwrap().0,
            Expression::VariableReference(
                "test".into()
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
                Literal::String("One Two$Three".into())
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
                 $x_0 and ending with $y_1 are '$x_0*$y_1?txt"
            ).unwrap().0,
            Expression::Concat(
                vec![
                    Expression::Literal(
                        Literal::String("The value of $test is ".into())
                    ),
                    Expression::VariableReference(
                        "test".into()
                    ),
                    Expression::Literal(
                        Literal::String(
                            " and txt files starting with $x_0 and ending with \
                             $y_1 are ".into()
                        )
                    ),
                    Expression::VariableReference(
                        "x_0".into()
                    ),
                    Expression::Glob(Glob::Many),
                    Expression::VariableReference(
                        "y_1".into()
                    ),
                    Expression::Glob(Glob::One),
                    Expression::Literal(Literal::String("txt".into())),
                ]
            ) 
        );
    }
}