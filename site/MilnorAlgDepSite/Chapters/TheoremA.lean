import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep
-- Redundant once the supervisor regenerates `MilnorAlgDep.lean` to import every module.
import MilnorAlgDep.StepB.Abstract

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "Proof of Theorem A" =>
%%%
tag := "sec:main"
%%%

The proof of {cref "thm:A"}[] proceeds in three steps.
Step A shows that $`\psi(x)` and $`\psi(1-x)` have the same level; Step B extracts from
$`\psi` a function $`t` on $`K` and shows that it is a field embedding $`\tau`; Step C identifies
$`\psi` with a rational multiple of $`[\tau]`.

In the formalization the two characteristics are treated separately (see
{cref "sec:formalization"}[]): Step A and the adapted model are only needed in
characteristic $`p`, and Step B is proved once, abstractly, for both.

# Reductions and notation

The homomorphism $`\psi` extends uniquely to the perfect closure of $`K`, and
$`V_{L|l} = V_{L^i|l^i}`; so we may assume that $`K` and $`L` are perfect.
The basic tool is the consequence
$$`\psi(x + y) = \psi(y) + \psi\bigl(1 - (-x/y)\bigr)`
of (A1) and (A2), for $`x, y \in K^\times` with $`x + y \neq 0` and $`x/y \notin k`.

# Step A: the levels of ψ(x) and ψ(1 − x)
%%%
tag := "sec:stepA"
%%%

:::prop "6.1" (tag := "prop:levels")
For every $`x \in K \sm k` we have $`\lev \psi(1-x) = \lev \psi(x)`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/StepA.lean` (work package WP-P4).

# The adapted model
%%%
tag := "ss:model"
%%%

Extend representatives of $`\psi(x_1), \dots, \psi(x_d)` to a transcendence basis $`A` of
$`L|l`, put $`F = L_A` and $`\Omega = \Omega_{L_A|l}`, and work with the subgroup
$`W \subset V` of elements of non-negative height, on which there is a logarithmic derivative
$`\dlog_A \colon W \to \Omega`.

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/AdaptedModel.lean` (work package WP-P5).

# Step B: the functions μ and t

For a primitive $`x`, define $`\mu(x)` by $`\Delta(1-x) = \mu(x) \Delta(x)` and put
$$`t(x) = \frac{\mu(x)}{\mu(x) - 1}.`
The one- and two-variable lemmas (Lemmas 6.6 and 6.7) give the functional equations of $`t`.

The formalization proves Step B once, for an abstract homomorphism $`\Delta` from the
multiplicative group of a field into a vector space, subject to the hypotheses that the adapted
model provides in characteristic $`p` and that $`\Omega_{L|l}` provides directly in
characteristic $`0`:

{docstring MilnorAlgDep.StepBData}

# The field embedding

:::prop "6.9" (tag := "prop:tau")
$`\tau \colon K_0 \to F` is a field embedding.
In particular $`K` and $`L` have the same characteristic.
:::

In the abstract setting, the embedding is a ring homomorphism $`\tau \colon K \to F` with
$`\tau(x) = t(x)` for every primitive $`x`:

{docstring MilnorAlgDep.StepBData.exists_ringHom}

# Step C: identification

:::prop "6.12" (tag := "prop:rational")
There is $`r \in \QQ^\times` with $`\psi(x) = r \, [\tau(x)]` for all $`x \in K_0^\times`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/StepC.lean` (work package WP-P6).

# End of the proof

The embedding $`\tau` extends to $`K`, and $`\tau^{-1}(l) = k`; it remains to prove uniqueness.

:::lem "6.13" (tag := "lem:unique")
Let $`\tau, \tau' \colon K \to L` be field embeddings with $`\tau^{-1}(l) = \tau'^{-1}(l) = k \neq K`,
and $`r, r' \in \QQ^\times` with $`r[\tau(x)] = r'[\tau'(x)]` in $`V` for all $`x \in K^\times`.
Then $`\tau' = \Frob^j \circ \tau` and $`r' = p^{-j} r` for some $`j \in \Gamma`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/Uniqueness.lean` (work package WP-U).
