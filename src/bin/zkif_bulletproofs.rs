extern crate bincode;
extern crate bulletproofs;
extern crate zkinterface;

use std::env;
use std::io::{stdin, Read, Write};
use std::fs::{File, create_dir_all};
use std::path::Path;
use zkinterface::{Result, reading::Messages};
use bulletproofs::r1cs::{zkinterface_backend, R1CSProof};

const USAGE: &str = "Bulletproofs proving system.

    zkif_bulletproofs prove  [proof_path]
    zkif_bulletproofs verify [proof_path]

";

const DEFAULT_PROOF_PATH: &str = "bulletproofs-proof";

pub fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    let args: Vec<&str> = args.iter().map(|a| &a[..]).collect();
    if args.len() <= 1 {
        eprintln!("{}", USAGE);
        return Err("Missing command.".into());
    }

    let command = args[1];

    let proof_path = if args.len() == 2 { DEFAULT_PROOF_PATH } else { args[2] };
    let proof_path = Path::new(proof_path);
    if let Some(parent) = proof_path.parent() {
        create_dir_all(parent)?;
    }

    let read = || -> Result<Messages> {
        let mut messages = Messages::new();
        messages.read_from(&mut stdin())?;
        Ok(messages)
    };

    match &command[..] {
        "prove" => main_prove(read()?, proof_path),
        "verify" => main_verify(read()?, proof_path),
        _ => {
            eprintln!("{}", USAGE);
            Err(format!("Unknown command {}", command).into())
        }
    }
}

fn main_prove(messages: Messages, proof_path: &Path) -> Result<()> {
    let proof = zkinterface_backend::prove(&messages)?;

    // Save to file.
    let proof_ser = bincode::serialize(&proof)?;
    File::create(proof_path)?.write_all(&proof_ser)?;

    eprintln!("Saved proof into {}", proof_path.display());
    Ok(())
}

fn main_verify(messages: Messages, proof_path: &Path) -> Result<()> {
    eprintln!("Verifying proof in {}", proof_path.display());

    // Load from file.
    let mut proof_ser = Vec::new();
    File::open(&proof_path)?.read_to_end(&mut proof_ser)?;
    let proof: R1CSProof = bincode::deserialize(&proof_ser)?;

    zkinterface_backend::verify(&messages, &proof)
}