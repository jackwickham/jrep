use std::fs::File;

mod pattern;
mod async_impl;
mod sync_impl;

fn main() {
    let mut args = std::env::args().peekable();
    let mut use_sync = false;

    args.next();

    while let Some(peek_arg) = args.peek() {
        if peek_arg.starts_with("--") {
            let arg = args.next().unwrap();
            match arg.as_str() {
                "--sync" => {
                    use_sync = true;
                },
                unknown => panic!("Unknown flag argument {}", unknown),
            }
        } else {
            break;
        }
    }

    let pattern = args.next().unwrap();
    let file_path = args.next().unwrap();

    if pattern.len() == 0 {
        panic!("A pattern must be provided");
    }
    // We need enough space left in the buffer to read the whole match and backtrack
    if pattern.len() > (2 << 16) {
        panic!("Pattern too long");
    }

    let file = File::open(file_path).unwrap();

    let matches = if use_sync {
        sync_impl::search_file(file, &pattern).unwrap()
    } else {
        async_impl::search_file(file, &pattern).unwrap()
    };
    if matches.len() > 0 {
        for m in matches {
            println!("{}", m);
        }
        std::process::exit(0);
    } else {
        std::process::exit(1);
    }
}
