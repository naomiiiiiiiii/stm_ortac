type frontend = Default | Monolith | STM

let get_channel = function None -> stdout | Some path -> open_out path

let frontend_printer ppf = function
  | Default -> Fmt.string ppf "Default"
  | Monolith -> Fmt.string ppf "Monolith"
  | STM -> Fmt.string ppf "STM"

let frontend_parser = function
  | "default" -> Ok Default
  | "monolith" -> Ok Monolith
  | "STM" -> Ok STM
  | s -> Error (`Msg (Fmt.str "Error: `%s' is not a valid argument" s))

let main frontend input output () =
  let channel = get_channel output in
  try
    match frontend with
    | Default -> Ortac_default.generate input channel
    | Monolith -> Ortac_monolith.generate input channel
| STM -> Ortac_STM.generate input channel
  with Gospel.Warnings.Error e ->
    Fmt.epr "%a@." Gospel.Warnings.pp e;
    exit 1

open Cmdliner

let setup_log =
  let init style_renderer = Fmt_tty.setup_std_outputs ?style_renderer () in
  Term.(const init $ Fmt_cli.style_renderer ())

let output_file =
  let parse s =
    match Sys.is_directory s with
    | true -> Error (`Msg (Fmt.str "Error: `%s' is a directory" s))
    | false | (exception Sys_error _) -> Ok (Some s)
  in
  Arg.(
    value
    & opt (conv ~docv:"OUTPUT" (parse, Fmt.(option string))) None
    & info [ "o"; "output" ] ~docv:"OUTPUT")

let ocaml_file =
  let parse s =
    match Sys.file_exists s with
    | true ->
        if Sys.is_directory s || Filename.extension s <> ".mli" then
          `Error (Fmt.str "Error: `%s' is not an OCaml interface file" s)
        else `Ok s
    | false -> `Error (Fmt.str "Error: `%s' not found" s)
  in
  Arg.(required & pos 0 (some (parse, Fmt.string)) None & info [] ~docv:"FILE")

let frontend =
  Arg.(
    value
    & opt (conv ~docv:"FRONTEND" (frontend_parser, frontend_printer)) Default
    & info [ "f"; "frontend" ] ~docv:"FRONTEND")

let cmd =
  let doc = "Run ORTAC." in
  let version = "ortac version %%VERSION%%" in
  let info = Cmd.info "ortac" ~doc ~version in
  let term =
    Term.(const main $ frontend $ ocaml_file $ output_file $ setup_log)
  in
  Cmd.v info term

let () = Stdlib.exit (Cmd.eval cmd)
