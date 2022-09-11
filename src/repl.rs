use crate::*;
use context::Context;
use user_input::UserInput;

/// The main loop of the repl.
pub fn main() {
    use UserInput::*;

    println!("=== HOOO 0.1 ===");
    println!("For more information, type `help`");

    let mut context = Context::new();

    loop {
        use std::io::{self, Write};

        let mut input = String::new();
        print!("> ");
        io::stdout().flush().unwrap();
        match io::stdin().read_line(&mut input) {
            Ok(_) => {}
            Err(_) => {
                println!("ERROR: Could not read input");
                continue;
            }
        };

        let user_input = UserInput::from_str(&input).refine(&context);
        if let Bye = user_input {break};
        if let Err(err) = context.handle(user_input) {
            eprintln!("ERROR:\n{}", err);
        }
    }
}
