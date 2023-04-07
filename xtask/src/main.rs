use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{self, Command};

use clap::{Parser, Subcommand};

mod generate_tests;

#[derive(Parser)]
struct Args {
    /// The command to run.
    #[command(subcommand)]
    task: Task,
}

#[derive(Subcommand)]
enum Task {
    /// Generate integration test suite.
    Codegen,
    /// Generate docs.
    #[command(disable_help_flag = true)]
    Doc {
        #[arg(allow_hyphen_values = true, trailing_var_arg = true)]
        rest: Vec<OsString>,
    },
    /// Format code.
    #[command(disable_help_flag = true)]
    Fmt {
        #[arg(allow_hyphen_values = true, trailing_var_arg = true)]
        rest: Vec<OsString>,
    },
}

fn run_command(command: &mut Command) {
    if !command.status().unwrap().success() {
        process::exit(1)
    }
}

fn main() {
    let args = Args::parse();

    match args.task {
        Task::Codegen => {
            generate_tests::main();
            // Reformat the test code now.
            run_command(Command::new("cargo").args(["+nightly", "fmt", "-p", "purl_test"]));
        },
        Task::Doc { rest } => {
            run_command(
                Command::new("cargo")
                    .env(
                        "RUSTDOCFLAGS",
                        format!("--cfg docsrs {}", env::var("RUSTDOCFLAGS").unwrap_or_default()),
                    )
                    .args(["+nightly", "doc", "--all-features"])
                    .args(rest),
            );
        },
        Task::Fmt { rest } => {
            run_command(Command::new("cargo").args(["+nightly", "fmt"]).args(rest));
        },
    }
}

fn workspace_dir() -> PathBuf {
    Path::new(&env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_owned()
}
