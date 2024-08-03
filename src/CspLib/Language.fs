module CspLib.Language

type Branch<'a, 'b> =
  { value: 'a
    children: Tree<'a, 'b> list }

and Tree<'a, 'b> =
  | Branch of Branch<'a, 'b>
  | Leaf of 'b

type EventId = EventId of string
type CspEvent = { name: EventId; description: string }
type ProcessId = ProcessId of string

type ProcessDef =
  { name: ProcessId
    localRecursion: ProcessId option
    alphabet: EventId list
    body: Tree<CspEvent, ProcessId> }

type Statement =
  | ProcessDef of ProcessDef
  | EventDef of CspEvent

type CspModule =
  { name: string
    imports: string list
    definitions: Statement list }
