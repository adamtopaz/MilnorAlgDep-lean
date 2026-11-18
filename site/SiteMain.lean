import VersoManual
import MilnorAlgDepSite

/-!
Renders the companion text. Run through the Lean interpreter, so that Mathlib is never compiled
to native code:

    lake run versoMain SiteMain.lean --output _out

(`build.sh` does this, after checking the dependency pins.) Accepts Verso's usual flags, for
example `--draft` or `--verbose`.
-/

open Verso.Genre Manual

def main := manualMain (%doc MilnorAlgDepSite) (config := MilnorAlgDepSite.siteConfig)
