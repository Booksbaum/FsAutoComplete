namespace FsAutoComplete

open FSharp.Compiler.SourceCodeServices
open System
open FsAutoComplete.Logging
open FSharp.UMX
open FSharp.Compiler.Text
open System.Runtime.CompilerServices

type VolatileFile =
  { Touched: DateTime
    Lines: ISourceText
    Version: int option }

open System.IO


[<Extension>]
type SourceTextExtensions =
  [<Extension>]
  static member GetText(t: ISourceText, m: FSharp.Compiler.Text.Range): Result<string, string> =
    let allFileRange = Range.mkRange m.FileName Pos.pos0 (t.GetLastFilePosition())
    if not (Range.rangeContainsRange allFileRange m)
    then Error "%A{m} is outside of the bounds of the file"
    else
      if m.StartLine = m.EndLine then // slice of a single line, just do that
        let lineText = t.GetLineString (m.StartLine - 1)
        lineText.Substring(m.StartColumn, m.EndColumn - m.StartColumn) |> Ok
      else
        // multiline, use a builder
        let builder = new System.Text.StringBuilder()
        // slice of the first line
        let firstLine = t.GetLineString (m.StartLine - 1)
        builder.Append (firstLine.Substring(m.StartColumn)) |> ignore<System.Text.StringBuilder>
        // whole intermediate lines
        for line in (m.StartLine + 1)..(m.EndLine - 1) do
          builder.AppendLine (t.GetLineString(line - 1)) |> ignore<System.Text.StringBuilder>
        // final part, potential slice
        let lastLine = t.GetLineString (m.EndLine - 1)
        builder.Append (lastLine.Substring(0, m.EndColumn)) |> ignore<System.Text.StringBuilder>
        Ok (builder.ToString())

  [<Extension>]
  static member inline Lines(t: ISourceText) =
    Array.init (t.GetLineCount()) t.GetLineString

  [<Extension>]
  /// a safe alternative to GetLastCharacterPosition, which returns untagged indexes. this version
  /// returns a FCS Pos to prevent confusion about line index offsets
  static member GetLastFilePosition(t: ISourceText): FSharp.Compiler.Text.Pos =
    let endLine, endChar = t.GetLastCharacterPosition()
    Pos.mkPos endLine endChar

type FileSystem (actualFs: IFileSystem, tryFindFile: string<LocalPath> -> VolatileFile option) =
    let getContent (filename: string<LocalPath>) =
         filename
         |> tryFindFile
         |> Option.map (fun file -> file.Lines.ToString() |> System.Text.Encoding.UTF8.GetBytes)

    let fsLogger = LogProvider.getLoggerByName "FileSystem"
    let testLogger = LogProvider.getLoggerByName "TestSystem"
    /// translation of the BCL's Windows logic for Path.IsPathRooted.
    ///
    /// either the first char is '/', or the first char is a drive identifier followed by ':'
    let isWindowsStyleRootedPath (p: string) =
        let isAlpha (c: char) =
            (c >= 'A' && c <= 'Z')
            || (c >= 'a' && c <= 'z')
        (p.Length >= 1 && p.[0] = '/')
        || (p.Length >= 2 && isAlpha p.[0] && p.[1] = ':')

    /// translation of the BCL's Unix logic for Path.IsRooted.
    ///
    /// if the first character is '/' then the path is rooted
    let isUnixStyleRootedPath (p: string) =
        p.Length > 0 && p.[0] = '/'

    interface IFileSystem with
        (* for these two members we have to be incredibly careful to root/extend paths in an OS-agnostic way,
           as they handle paths for windows and unix file systems regardless of your host OS.
           Therefore, you cannot use the BCL's Path.IsPathRooted/Path.GetFullPath members *)

        member _.IsPathRootedShim (p: string) =
          let r =
            isWindowsStyleRootedPath p
            || isUnixStyleRootedPath p
          fsLogger.debug (Log.setMessage "Is {path} rooted? {result}" >> Log.addContext "path" p >> Log.addContext "result" r)
          r

        member _.GetFullPathShim (f: string) =
          //error!
          let expanded =
            Path.FilePathToUri f
            |> Path.FileUriToLocalPath
          fsLogger.debug (Log.setMessage "{path} expanded to {expanded}" >> Log.addContext "path" f >> Log.addContext "expanded" expanded)

          let log (values: (string*obj) list) =
            let l = values |> List.map (fst >> String.length) |> List.max
            let msg = 
              values
              |> List.map (fun (n, _) -> sprintf "* %-*s = {%s}" l n n)
              |> String.concat "\n"
              |> sprintf "GetFullPathShim:\n%s\n"

            values
            |> List.fold (
              fun l (n, v) ->
                l >> Log.addContextDestructured n v
            ) (Log.setMessage msg)
            |> testLogger.info


          // expanded
          // actualFs.GetFullPathShim f
          // expanded.Replace("/", "\\")
          match System.Environment.OSVersion.Platform with
          | PlatformID.Win32NT | PlatformID.Win32S | PlatformID.Win32Windows | PlatformID.WinCE ->
              let ensureForwardSlash (str: string) =
                str.Replace("\\", "/")
              let ensureBackwardSlash (str: string) =
                str.Replace("/", "\\")
              let ensureChaos (str: string) =
                // alternate slash direction to provoke errors

                // special treatment for leading double slashes (network drive)
                let (str, start) =
                  if str.StartsWith "//" || str.StartsWith "\\\\" then
                    (str.Substring(2), true)
                  else
                    (str, false)
                  
                let str =
                  str.Split('/', '\\')
                  |> Array.fold (fun (str, back) p -> 
                      let p =
                        if str |> String.IsNullOrWhiteSpace then
                          p
                        else
                          let s = if back then '\\' else '/'
                          sprintf "%s%c%s" str s p
                      (p, not back)
                  ) ("", false)
                  |> fst

                if start then
                  sprintf "//%s" str
                else
                  str

              if false then
                ""
              // for `GoToTests.fs` -> `lsp.Ionide WorkspaceLoader.Go to definition tests.GoTo Tests.Go-to-type-definition on property`
              // -> test Goto type on Property of type `string option` -> in `prim-types.fsi`
              // GetFullPathShim:
              // * path     = "E:\A\_work\130\s\src\fsharp\FSharp.Core\prim-types.fsi"
              // * uri      = "file:///E%3A/A/_work/130/s/src/fsharp/FSharp.Core/prim-types.fsi"
              // * expanded = "E:/A/_work/130/s/src/fsharp/FSharp.Core/prim-types.fsi"
              // * return   = "E:/A/_work/130/s/src/fsharp/FSharp.Core/prim-types.fsi"
              //               ^^^^^^ ok
              // * actualFs = "E:\A\_work\130\s\src\fsharp\FSharp.Core\prim-types.fsi"
              //               ^^^^^^ not ok
              // Note: doesn't exists on local -> from source (debug data)
              // Note: all other don't matter for this test...
              else if expanded.EndsWith "prim-types.fsi" then
                expanded |> ensureForwardSlash
              else if expanded.EndsWith ".fsi" then
                expanded |> ensureForwardSlash
              // for `Program.fs` -> `lsp.Ionide WorkspaceLoader.windows error.script test`
              // GetFullPathShim:
              // * path     = "e:\prog\fsharp\editor\ionide\FsAutoComplete\test\FsAutoComplete.Tests.Lsp\TestCases\Completion\Script.fsx"
              // * uri      = "file:///e%3A/prog/fsharp/editor/ionide/FsAutoComplete/test/FsAutoComplete.Tests.Lsp/TestCases/Completion/Script.fsx"
              // * expanded = "e:/prog/fsharp/editor/ionide/FsAutoComplete/test/FsAutoComplete.Tests.Lsp/TestCases/Completion/Script.fsx"
              // * return   = "e:\prog\fsharp\editor\ionide\FsAutoComplete\test\FsAutoComplete.Tests.Lsp\TestCases\Completion\Script.fsx"
              // * actualFs = "e:\prog\fsharp\editor\ionide\FsAutoComplete\test\FsAutoComplete.Tests.Lsp\TestCases\Completion\Script.fsx"
              // Note: ONLY script file -- other resolved paths are all dll, fs, fsi
              else if expanded.EndsWith ".fsx" then
                // expanded |> ensureChaos // error
                // expanded |> ensureForwardSlash // error
                expanded |> ensureBackwardSlash // ok
              // pdb files not resolved via GetFullPathShim
              // else if expanded.EndsWith ".pdb" then
              //   expanded |> ensureForwardSlash
              // for `GoToTests.fs` -> `lsp.Ionide WorkspaceLoader.Go to definition tests.GoTo Tests.Go-to-implementation on sourcelink file with sourcelink in PDB`
              // * pdb files aren't resolved via FileSystem, but path seems to be generated based on fs-files handled here.
              //   But that result isn't normalized again -> required forward slashes to work
              // otherwise:
              // ```
              // [Expecto 00:00:04.3241963] FsAutoComplete.Tests.Lsp: [W] 2021-06-21T17:46:17.1679077+00:00: No sourcelinked source file matched "C:\projects/giraffe\src/Giraffe\GiraffeViewEngine.fs". Available documents were (normalized paths here): ["C:/projects/giraffe/src/Giraffe/Middleware.fs", "C:/projects/giraffe/src/Giraffe/HttpStatusCodeHandlers.fs", "C:/projects/giraffe/src/Giraffe/Negotiation.fs", "C:/projects/giraffe/src/Giraffe/Streaming.fs", "C:/projects/giraffe/src/Giraffe/Preconditional.fs", "C:/projects/giraffe/src/Giraffe/ResponseWriters.fs", "C:/projects/giraffe/src/Giraffe/Routing.fs", "C:/projects/giraffe/src/Giraffe/Auth.fs", "C:/projects/giraffe/src/Giraffe/ModelValidation.fs", "C:/projects/giraffe/src/Giraffe/ModelBinding.fs", "C:/projects/giraffe/src/Giraffe/GiraffeViewEngine.fs", "C:/projects/giraffe/src/Giraffe/ResponseCaching.fs", "C:/projects/giraffe/src/Giraffe/Core.fs", "C:/projects/giraffe/src/Giraffe/FormatExpressions.fs", "C:/projects/giraffe/src/Giraffe/Serialization.fs", "C:/projects/giraffe/src/Giraffe/ComputationExpressions.fs", "C:/projects/giraffe/src/Giraffe/Common.fs"] [Serilog]
              // ```
              //todo: most likely same for `.fsi`
              else if expanded.EndsWith ".fs" then
                expanded |> ensureForwardSlash
              // else if expanded.EndsWith ".fsi" then
              //   expanded |> ensureBackwardSlash
              // else if expanded.EndsWith ".dll" then
              //   expanded |> ensureForwardSlash
              else
                // expanded.Replace("/", "\\")
                // expanded
                // alternate between `/` and `\` to provoke errors
                expanded |> ensureChaos
              //todo: network drive?
          | _ -> expanded
          |> fun p ->
              log [
                ("path", box f)
                ("uri", box <| Path.FilePathToUri f)
                ("expanded", box expanded)
                ("return", box p)
                ("actualFs", box <| actualFs.GetFullPathShim f)
              ]
              p


        (* These next members all make use of the VolatileFile concept, and so need to check that before delegating to the original FS implementation *)

        (* Note that in addition to this behavior, we _also_ do not normalize the file paths anymore for any other members of this interfact,
           because these members are always used by the compiler with paths returned from `GetFullPathShim`, which has done the normalization *)

        member _.ReadAllBytesShim (f) =
          f
          |> Utils.normalizePath
          |> getContent
          |> Option.defaultWith (fun _ -> actualFs.ReadAllBytesShim f)

        member _.FileStreamReadShim (f) =
          f
          |> Utils.normalizePath
          |> getContent
          |> Option.map (fun bytes -> new MemoryStream(bytes) :> Stream)
          |> Option.defaultWith (fun _ -> actualFs.FileStreamReadShim f)

        member _.GetLastWriteTimeShim (f) =
          f
          |> Utils.normalizePath
          |> tryFindFile
          |> Option.map (fun f -> f.Touched)
          |> Option.defaultWith (fun _ -> actualFs.GetLastWriteTimeShim f)

        member _.FileStreamCreateShim (f) = actualFs.FileStreamCreateShim f
        member _.FileStreamWriteExistingShim (f) = actualFs.FileStreamWriteExistingShim f
        member _.IsInvalidPathShim (f) = actualFs.IsInvalidPathShim f
        member _.GetTempPathShim () = actualFs.GetTempPathShim()
        member _.SafeExists (f) = actualFs.SafeExists f
        member _.FileDelete (f) = actualFs.FileDelete f
        member _.AssemblyLoadFrom (f) = actualFs.AssemblyLoadFrom f
        member _.AssemblyLoad (f) = actualFs.AssemblyLoad f
        member _.IsStableFileHeuristic (f) = actualFs.IsStableFileHeuristic f
