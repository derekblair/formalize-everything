import SonnetForm.Corpus

/-! Every component and each line's license attribution are part of the proved
row; the deviation catalogue is generated from exactly these expected rows. -/
namespace SonnetForm

structure LineDiagnostic where
  strict : Bool
  licensed : Bool
  licenses : List License
  rhyme : Option String
  selectedScan : Option Scan
  deriving Repr, BEq, DecidableEq

structure AuditRow where
  components : Verdict
  lines : List LineDiagnostic
  deriving Repr, BEq, DecidableEq

def inspectLine (l : Line) : LineDiagnostic :=
  ⟨lineMeterStrict l, lineMeterLicensed l, lineLicenses l, l.rhyme,
    (l.scans.find? scanLicensed).or l.scans.head?⟩

def inspectSonnet (s : Sonnet) : AuditRow :=
  ⟨verdict s, s.lines.map inspectLine⟩

end SonnetForm
