use logos::Logos;

pub type Spanned<Tok, Loc, Error> = Result<(Loc, Tok, Loc), Error>;

#[derive(thiserror::Error, Debug, Clone)]
#[error("lexer error: {0}")]
pub struct LexerError(pub String);

#[derive(Debug, Clone, Logos, derive_more::Display, PartialEq)]
pub enum Token<'input> {
    #[token("let", priority = 100)]
    #[display(fmt = "let")]
    Let,
    #[token("cmd", priority = 100)]
    #[display(fmt = "cmd")]
    Cmd,
    #[token("capture", priority = 100)]
    #[display(fmt = "capture")]
    Capture,
    #[token("in", priority = 100)]
    #[display(fmt = "in")]
    In,
    #[token("int", priority = 100)]
    #[display(fmt = "int")]
    Int,
    #[token("str", priority = 100)]
    #[display(fmt = "str")]
    Str,
    #[token("any", priority = 100)]
    #[display(fmt = "any")]
    Any,
    #[token(">")]
    #[display(fmt = ">")]
    OutRedir,
    #[token("[")]
    #[display(fmt = "[")]
    LBracket,
    #[token("]")]
    #[display(fmt = "]")]
    RBracket,
    #[token("{")]
    #[display(fmt = "{{")]
    LBrace,
    #[token("}")]
    #[display(fmt = "}}")]
    RBrace,
    #[token("<")]
    #[display(fmt = "<")]
    InRedir,
    #[token(">>")]
    #[display(fmt = ">>")]
    AppendRedir,
    #[token("(")]
    #[display(fmt = "(")]
    LParen,
    #[token(")")]
    #[display(fmt = ")")]
    RParen,
    #[token("||")]
    #[display(fmt = "||")]
    Or,
    #[token("&&")]
    #[display(fmt = "&&")]
    And,
    #[token("=")]
    #[display(fmt = "=")]
    Equal,
    #[token("=>")]
    #[display(fmt = "=>")]
    Arrow,
    #[regex("[a-zA-Z0-9_]+", priority = 10)]
    #[display(fmt = "identifier({})", _0)]
    Identifier(&'input str),
    #[regex(r"[\w\d:+\-_/.$]+", callback = |lex| lex.slice())]
    #[display(fmt = "word({})", _0)]
    Word(&'input str),
    #[token("$(")]
    #[display(fmt = "$(")]
    SubShell,
    #[regex(r#"'(\\[^\n]|[^'\n])*'"#, |lex| {
        lex.slice()
    })]
    #[display(fmt = "string({})", _0)]
    StrLitteral(&'input str),
    #[regex(r#""(\\[^\n]|[^"\n])*""#, |lex| {
        let s = lex.slice();
        &s[1..s.len() - 1]
    })]
    #[display(fmt = "istring({})", _0)]
    InterpolatedString(&'input str),
    #[regex(r"[0-9_]+", priority = 30, callback = |lex| {
        lex
            .slice()
            .bytes()
            .filter(|&b| b != b'_')
            .fold(0, |current, digit| 10*current + (digit - b'0') as i64)
    })]
    #[display(fmt = "int({})", _0)]
    IntNum(i64),
    #[token("\n")]
    #[display(fmt = "\\n")]
    Newline,
    #[token(",")]
    #[display(fmt = ",")]
    Comma,
    #[token(";")]
    #[display(fmt = ";")]
    Semicolon,
    #[token(":")]
    #[display(fmt = ":")]
    Colon,
    #[token("|")]
    #[display(fmt = "|")]
    Pipe,
    #[error]
    #[regex(r"#[^\n]*\n", logos::skip)]
    #[regex(r"[ \t]", logos::skip)]
    #[display(fmt = "error")]
    Error,
}

pub fn lexer<'input>(
    input: &'input str,
) -> impl Iterator<Item = Spanned<Token<'input>, usize, LexerError>> + 'input {
    Token::lexer(input)
        .spanned()
        /* .inspect(|x| {
            dbg!(x);
        }) */
        .map(move |(token, span)| match token {
            Token::Error => Err(LexerError(format!("Unknown token: {:?}", &input[span]))),
            v => Ok((span.start, v, span.end)),
        })
}
