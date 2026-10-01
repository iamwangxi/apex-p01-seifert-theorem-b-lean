# Contractibility of exchange complexes

Lean 4 / Mathlib formalization of **Theorem B** in Apex Intelligence,
[*Contractibility of the complex of incompressible Seifert surfaces: the knot case of
Kakimizu's problem*](https://math.apexin.net/papers/seifert-surfaces.pdf): every
nonempty connected exchange complex is contractible. `Seifert.theoremB` proves the
result; `SeifertAudit.theoremB_verified` proves an independent, Mathlib-only statement.
Vertices and complexity values have independent universes. There is no finiteness,
countability, local finiteness or dimension bound.

The repository also proves the **conditional** implications from the output properties
of Theorem 5.1 to Proposition 5.2, the exchange structure, Theorem A, the genus family
of Theorem C, and the lexicographic area family actually proved in §6.2. It proves the
topological, order and countability conclusions of Lemma 4.8(ii)–(iv) from the finiteness premise (i),
and supplies a conditional Theorem D alias for link-version geometric inputs. Both
truncation conclusions require the truncated set to be nonempty. The knot, link, surface
and minimal-area geometry supplying those inputs has not been formalized.

Reference version: the 48-page competition PDF, SHA-256
`34f17d7d99780d3fd3626d9e5d7b35d6aa76661c404f191b6df341b300c0c06f`.
This reference digest identifies the supplied paper; the paper is not bundled here.
Its acknowledgement that Theorem B was not yet formalized describes the paper's earlier
state. This repository supplies a later proof of Theorem B with the routes below.

## Statements and geometric model

[Statements.lean](Statements.lean) imports only Mathlib. An exchange complex is
`Nonempty V ∧ G.Preconnected ∧ ExchangeStructure G c`, with `[LinearOrder W]` and
`[WellFoundedLT W]`. For each pair with **actual** extended graph distance
`G.edist u v = 2`, N1 requires an apex of the entire common-neighbour set; N2 requires
one such apex whose complexity is below `max (c u) (c v)`. The same witness must satisfy
both the apex and descent conditions. Complexity need not be injective.

The flag complex consists of every finite clique, including the empty face. A realization
point is a `Convexity.StdSimplex ℝ V`: finitely supported, nonnegative barycentric
weights summing to one, with clique support. The empty face supplies no point.
Each finite closed simplex has its usual simplex topology. The realization has the
**final topology of all these closed-simplex inclusions**, implemented as
`⨆ s, TopologicalSpace.coinduced (closedSimplex G s) inferInstance`.
The closed-set criterion is `Topo.Complex.isClosed_iff`, with independent-statement
versions `AdversarialAudit.statement_isClosed_iff` and
`AdversarialAudit.independent_closed_criterion`: a set is closed exactly when its
inverse image in every finite closed simplex is closed. The inclusions are closed
embeddings (`AdversarialAudit.statement_closedSimplex_closedEmbedding`).
`ContractibleSpace` is Mathlib's actual homotopy equivalence with `Unit`.

[ApplicationStatements.lean](ApplicationStatements.lean) also imports only Mathlib.
Its `SurfaceSystem` exposes positive area, connectedness (including nonemptiness),
well-foundedness of the **attained** lexicographic `(genus, area)` values, and
Theorem 5.1(a)–(d) as assumptions. The outputs `p, q` are chosen before the universally
quantified vertex `z` in clause (b). No apex, descent or contractibility is assumed.
`GenusSet g ℓ` is `{v | g v ≤ ℓ}`. `AreaSet g A ℓ a₀` is
`{v | g v < ℓ ∨ g v = ℓ ∧ A v ≤ a₀}`. For each nonempty such full subcomplex,
`FullConclusion` states connectedness, preservation of both natural and extended
edge-path distances, and contractibility in its own weak topology.

[SurfaceFiniteness.lean](Topo/SurfaceFiniteness.lean) uses these independent definitions.
Its `FiniteFibres g A` is Lemma 4.8(i): for every natural genus `h` and real cutoff `a`,
`{v | g v = h ∧ A v ≤ a}` is finite. Positive areas make this equivalent to the paper's
positive-cutoff version (`finiteFibres_iff_positive_cutoffs`). Counting distinct attained
areas strictly below each area gives `AreaValues g A h ↪o ℕ`; keeping the genus as the
first coordinate gives `Values g A ↪o ℕ ×ₗ ℕ`. These embeddings preserve and reflect
the original induced orders, proving the bounds ω and ω² and well-foundedness of `Values`.
Vertices are countable because they are the union over `h, n : ℕ` of the finite vertex
sets with `g v = h` and `A v ≤ n`. No positivity or injectivity is used in these proofs.
[SurfaceAreaTopology.lean](Topo/SurfaceAreaTopology.lean) completes Lemma 4.8(ii):
`areaValues_isClosed` proves that each `AreaValues g A h` is closed in ℝ, and
`areaValues_discreteTopology` proves that its usual subspace topology is discrete.
Every real point has an open neighborhood in which the area values lie in a finite
closed set; removing the other bounded values isolates each attained value.
These proofs also need neither positivity nor injectivity. With positive areas,
`areaValues_closed_discrete_positive` places all values in `Set.Ioi 0` and proves
closedness and the discrete subspace topology in that positive-real ambient space.

[SurfaceFiniteApplications.lean](Topo/SurfaceFiniteApplications.lean) defines
`SeifertApplicationStatement.SurfaceSystemOfFiniteFibres` and proves the independent
`theoremA_of_finiteFibres`, `theoremC_genus_of_finiteFibres`, and
`theoremC_area_of_finiteFibres`. Only the original well-foundedness premise is replaced
by (i); positive area, connectedness and all Theorem 5.1(a)–(d) quantifiers are unchanged.
With positive-area data retained as in Definition 4.7, the remaining geometric inputs
can now be reduced to connectedness, flagness (modeled by the clique complex),
Lemma 4.8(i), and Theorem 5.1(a)–(d). Neither an order-type bound nor well-foundedness
needs to be supplied separately.

## Paper-to-Lean correspondence

| Section 2 item | Lean declaration(s) | Role |
| --- | --- | --- |
| Definition 2.1 | `SeifertStatement.ExchangeStructure`, `ExchangeComplex`; `Seifert.distanceTwo_iff_edist` | Exact N1/N2 quantifiers, actual distance two and well-ordered complexity |
| Lemma 2.2 | `Seifert.ties_may_be_broken`, `tieComplexity_wellOrdersVertices`; `AdversarialAudit.lemma22_full_conclusion` | Lexicographic tie refinement, injectivity and a well-order on vertices |
| Corollary 2.3 | `Seifert.bounded_geodesic`, `downward_dist_eq`, `downward_edist_eq`, `downward_preconnected`, `downward_connected` | Bounded geodesics and isometric full subcomplexes; Connected requires nonemptiness |
| Lemma 2.4 | `Seifert.downward_injectiveExchangeComplex`, `strictSublevel_injectiveExchangeComplex`, `descending_injectiveExchangeComplex`, `descendingLink_nonempty` | Heredity and the nonempty descending link away from the least vertex |
| Theorem B, base | `Seifert.contractible_sublevel_of_least` | The least sublevel is a one-vertex cone |
| Theorem B, successor | `Topo.Complex.sublevel_eq_attachCone`, `sublevel_cone_inter`, `contractible_sublevel`; `Seifert.injective_sublevel_contractible` | Attach the cone over the descending link; the induction is universal over graphs |
| Theorem B, limit | `Seifert.contractible_of_sublevels`; `Topo.Complex.contractible_of_cofinal_contractible`, `contractible_of_finiteInclusionsNull` | Finite subcomplexes fit in contractible stages; assemble an actual contraction |
| Theorem B, conclusion | `Seifert.theoremB`, `SeifertAudit.theoremB_verified` | Remove the temporary injectivity convention and discharge the independent statement |

Names in the application table are in `Seifert.Application` unless qualified otherwise.
The Lemma 4.8 declarations and the names ending in `_of_finiteFibres` are in
`SeifertApplicationStatement`.

| Sections 4–6 item | Lean declaration(s) | Status |
| --- | --- | --- |
| Definition 4.7 | `complexity`, `Values`, `value` | Lexicographic genus/area, restricted to attained values; the geometric minimum is an input |
| Lemma 4.8(i) | `FiniteFibres`, `finiteFibres_iff_positive_cutoffs` | Geometric finite-fibre premise; equivalent to positive cutoffs for positive areas |
| Lemma 4.8(ii)–(iv) | `areaValues_finite_Iic`, `areaValues_isClosed`, `areaValues_discreteTopology`, `areaValues_closed_discrete_positive`, `areaValues_orderEmbedding`, `values_orderEmbedding`, `values_wellFounded`, `vertices_countable` | All conclusions proved from (i): closed and discrete area values (also in ℝ>0 with positive areas), finite bounded intersections, order types at most ω and ω², induced-order well-foundedness and countable vertices |
| Theorem 5.1(a)–(d) | `Outputs`, `SurfaceSystem.outputs` | Explicit geometric premise with the original existential/universal order |
| Proposition 5.2(1) | `Outputs.apices`, `apex_exists` | Both outputs are apices of the entire two-interval |
| Proposition 5.2(2) | `Outputs.local_descent`, `lower_apex_minimal`, `lower_apex_direct` | The paper's minimal-apex argument and a direct proof |
| Proposition 5.2(3), exchange structure | `lower_apex_genus`, `exchangeComplex` | Genus bound and N1/N2 derived from the outputs |
| Theorem A, §6.1 | `theoremA`; `SeifertApplicationAudit.theoremA_verified`; `theoremA_of_finiteFibres` | Conditional application of Theorem B, now also from Lemma 4.8(i) |
| Theorem C, §6.2 | `downward_tie`, `downward_fullConclusion`, `genus_downward`, `area_downward`, `theoremC_genus`, `theoremC_area`; their `SeifertApplicationAudit` bridges; `theoremC_genus_of_finiteFibres`, `theoremC_area_of_finiteFibres` | Tie refinement, Corollary 2.3, heredity and Theorem B, with explicit nonemptiness; also from (i) |
| Theorem D, §6.3 | `theoremD`; `theoremD_of_finiteFibres` | The same conditional theorem on arbitrary vertex types, with link-version geometric inputs as premises |

Section 6.3 ends by obtaining N1 and N2 “exactly as in the proof of Theorem A”, then
using Theorem B. The abstract conditional theorem applies to any vertex type, so the
same implication applies to the link complex once its connectedness, flagness, finite
genus/area sublevels and exchange outputs are supplied. `Seifert.Application.theoremD`
directly reuses `theoremA`, while the independent `theoremD_of_finiteFibres` reuses the
new finite-fibre version. These aliases do not prove the link geometry in §6.3, including
the vertex identification and the modifications of the frontier and exchange arguments.

## Proof routes and boundaries

The successor argument uses a **relative cone strong deformation retraction**, fixing
the base, followed by gluing. This replaces the paper's two CW quotient homotopy
equivalences. At limits, compact sets lie in finite subcomplexes; the theorem
“every finite subcomplex inclusion is null-homotopic ⇒ contractible” is proved by
compatible skeletal extension and contraction of a simplicial cone. This replaces the
homotopy-group/Whitehead argument. The conclusion is full contractibility.

- Corollary 2.3 needs a boundary correction at `D = ∅`: isometry and `Preconnected`
  remain valid; `Connected` requires `D.Nonempty`. Theorem B retains its nonempty premise.
- The introduction's second Theorem C family bounds area at every genus. The actual
  §6.2 proof uses the different set `AreaSet` above, bounding area only in genus `ℓ`.
  The formalization follows §6.2 and does not assert the introduction's different set.
  Both families require a vertex; the area version works for any real cutoff when nonempty.
  [RectangularTruncation.lean](Topo/Examples/RectangularTruncation.lean) exhibits a system
  satisfying all the abstract premises whose literal rectangular cutoff has a disconnected
  full subcomplex; this is not a counterexample involving actual knots.
- `lower_apex_direct` proves Proposition 5.2(2) from the output clauses without a
  well-order, positivity or connectedness. The paper's well-order-based proof is retained
  as `lower_apex_minimal`.

The following scope limits apply:

1. The model is the weak realization of a graph's finite clique complex. It does not
   establish the result for arbitrary metric realization topologies. The current API
   does not automatically transport an arbitrary supplied Mathlib abstract flag complex.
2. The successor and limit arguments use the replacements above. This is a complete
   proof of Theorem B, rather than a line-by-line transcription of every Section 2 proof.
3. The development is classical. It does not verify the paper's finer ZF claim about
   using choice only once, or supply a computable global apex selection or contraction.
4. Coverage comprises Theorem B and the associated combinatorial/topological lemmas,
   all conclusions of Lemma 4.8(ii)–(iv) from (i), and conditional A/C/D applications.
   Lemma 4.8(i)'s geometric finiteness proof and
   the geometry establishing the application premises remain outside the formalization.
   Theorems A, C and D and the entire paper are not unconditional geometric results here.
5. Local acceptance rebuilt every project module while reusing installed dependency
   caches. It did not rebuild all of Mathlib from uncached sources or independently
   check dependency checkout revisions through repository metadata.

Topology regression checks prove that two isolated vertices and an empty vertex set
are not contractible, and that a single edge is homeomorphic to the usual closed unit
interval. The seven-vertex example and infinite star are cones; the six-vertex descending
link satisfies the independent exchange hypotheses and is **not** a cone. All are part
of the default build, as is a non-cone conditional surface-system example.
The three-vertex path in
[RectangularTruncation.lean](Topo/Examples/RectangularTruncation.lean) also checks every
independent surface-system premise and distinguishes the disconnected rectangular cutoff
from §6.2's area family, which contains all three vertices and satisfies `FullConclusion`.
[SurfaceFiniteness.lean](Topo/Examples/SurfaceFiniteness.lean) adds an infinite vertex
example on `ℕ × Bool`, with tied complexity values and negative area, satisfying (i).
Its induced `Values` order embeds into `ℕ ×ₗ ℕ` and is well-founded, and its vertices
are countable. This checks that the new ordinal implications require neither positive
area nor injective complexity. All new modules and examples are in the default build.

## Build and verify

Requirements: elan, the pinned Lean toolchain, and Python 3.9 or newer. From the
repository root:

```sh
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get
lake build
python3 verification/verify.py
```

The first cache command installs the locked dependencies and can use the network.
Once dependencies are installed, verification runs offline, using only Python's standard
library and Lake/Lean. No repository history, `rg` or other utility is required.
For an offline replay using an already installed dependency tree, omit the cache command
and use `lake --no-cache build` before the Python command. To rebuild all project
modules from scratch, remove only `.lake/build`, retaining `.lake/packages`.

The verifier checks the two byte-frozen statement hashes, their Mathlib-only imports,
default-build coverage, `lake build`, fresh `#print axioms` for key declarations
(including Lemma 4.8's topological and ordinal consequences, finite-fibre applications and Theorem D),
every repository `.lean` file for banned proof holes/declarations and execution features,
and the README's machine-printed types. Only `maxRecDepth 4096` and
`maxHeartbeats 1000000` in `Topo/ExchangeSeven.lean` are permitted source `set_option`
commands; their locations are reported. Dependencies and private metadata are outside
the owned-source scan. Results, sanitized logs and a candidate fingerprint go to
`verification/results/`; `summary.json` records `PASS` or `FAIL`, and failure exits nonzero.
CI runs cache retrieval, the default build and the same verifier.

## File map

| Path | Contents |
| --- | --- |
| `Topo.lean` | Public aggregate importing proofs, statements and all audits |
| `Statements.lean`, `ApplicationStatements.lean` | Frozen, independently defined Mathlib-only specifications |
| `Topo/WeakRealization.lean`, `Basic.lean`, `Subcomplex.lean`, `Cone.lean` | Finite barycentric realizations, final topology and simplex/cone interfaces |
| `Topo/BlockDeformation.lean`, `StrongDeformation.lean`, `BlockGluing.lean`, `InfiniteBlocks.lean` | Relative strong deformation and gluing, including infinite families |
| `Topo/FiniteSubcomplexContractibility.lean`, `CompactSubcomplex.lean`, `FiniteNullContractible.lean`, `DirectedUnion.lean` | Finite-subcomplex null-homotopy, skeletal extension and limit assembly |
| `Topo/SuccessorContractibility.lean`, `ConeBase.lean`, `ConeCylinder.lean`, `ConeParameters.lean`, `RelativeConeDeformation.lean`, `ConeAttachment.lean`, `FlagSuccessor.lean` | Relative cone and successor-step proofs |
| `Topo/Exchange*.lean`, `CliqueBridge.lean` | Exchange axioms, geodesics, heredity, ties and Theorem B |
| `Topo/SurfaceSystem.lean`, `SurfaceTruncation.lean`, `Surface*Example*.lean`, `SurfaceCounterexample.lean` | Conditional applications and examples |
| `Topo/SurfaceFiniteness.lean`, `SurfaceAreaTopology.lean`, `SurfaceFiniteApplications.lean` | Lemma 4.8(i) ⇒ all conclusions (ii)–(iv), independent finite-fibre A/C corollaries and conditional D aliases |
| `Topo/Examples/` | Infinite simplex, cone attachment, finite exchange and infinite-star examples |
| `Topo/Audit.lean`, `Topo/Audit/` | Statement bridges, all dependency audits and adversarial regression checks |
| `verification/` | Acceptance script and fresh axiom/type-printing harnesses |

## Axioms, license and assistance

The key proofs depend only on `propext`, `Classical.choice` and `Quot.sound` (or subsets).
The verifier rejects any other transitive axiom dependency. These are ordinary Lean
kernel checks; finite examples use ordinary `decide`.

The repository's code is released under the [Apache License 2.0](LICENSE).
The formalization code was written by GPT models in OpenAI Codex under human guidance.
Anthropic Claude handled planning and independent review. It has not been certified
by a human expert.

## Complete machine-printed theorem types and core statements

Generated by `lake --no-cache env lean -Dformat.width=100 -Dpp.funBinderTypes=true
verification/Types.lean`. The outer theorem-statement aliases are unfolded; the printed
definitions and fields specify the remaining premises and full-subcomplex conclusion.
The verifier compares this block with fresh output.

<!-- BEGIN MACHINE TYPES -->
```text
SeifertAudit.theoremB_verified : ∀ (V : Type u) (W : Type w) [inst : LinearOrder W] [inst_1 : WellFoundedLT W]
  (G : SimpleGraph V) (c : V → W),
  SeifertStatement.ExchangeComplex G c → ContractibleSpace (SeifertStatement.WeakRealization G)
Seifert.theoremB : ∀ {V : Type u} {W : Type w} [inst : LinearOrder W] [inst_1 : WellFoundedLT W] {G : SimpleGraph V}
  {c : V → W}, Seifert.ExchangeComplex G c → ContractibleSpace (Seifert.cliqueComplex G).Realization
SeifertApplicationAudit.theoremA_verified : ∀ (V : Type u) (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ),
  SeifertApplicationStatement.SurfaceSystem G g A → ContractibleSpace (SeifertApplicationStatement.WeakRealization G)
SeifertApplicationAudit.theoremC_genus_verified : ∀ (V : Type u) (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ),
  SeifertApplicationStatement.SurfaceSystem G g A →
    ∀ (ℓ : ℕ),
      (∃ (v : V), g v ≤ ℓ) → SeifertApplicationStatement.FullConclusion G (SeifertApplicationStatement.GenusSet g ℓ)
SeifertApplicationAudit.theoremC_area_verified : ∀ (V : Type u) (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ),
  SeifertApplicationStatement.SurfaceSystem G g A →
    ∀ (ℓ : ℕ) (a₀ : ℝ),
      (SeifertApplicationStatement.AreaSet g A ℓ a₀).Nonempty →
        SeifertApplicationStatement.FullConclusion G (SeifertApplicationStatement.AreaSet g A ℓ a₀)
structure SeifertStatement.ExchangeStructure.{u, w} {V : Type u} {W : Type w} [LinearOrder W] (G : SimpleGraph V)
  (c : V → W) [WellFoundedLT W] : Prop
number of parameters: 6
fields:
  SeifertStatement.ExchangeStructure.n1 : ∀ (u v : V), G.edist u v = 2 → ∃ (x : V), SeifertStatement.IsApex G u v x
  SeifertStatement.ExchangeStructure.n2 : ∀ (u v : V),
      G.edist u v = 2 → ∃ (x : V), SeifertStatement.IsApex G u v x ∧ c x < max (c u) (c v)
constructor:
  SeifertStatement.ExchangeStructure.mk.{u, w} {V : Type u} {W : Type w} [LinearOrder W] {G : SimpleGraph V} {c : V → W}
    [WellFoundedLT W] (n1 : ∀ (u v : V), G.edist u v = 2 → ∃ (x : V), SeifertStatement.IsApex G u v x)
    (n2 : ∀ (u v : V), G.edist u v = 2 → ∃ (x : V), SeifertStatement.IsApex G u v x ∧ c x < max (c u) (c v)) :
    SeifertStatement.ExchangeStructure G c
def SeifertStatement.ExchangeComplex.{u, w} : {V : Type u} →
  {W : Type w} → [inst : LinearOrder W] → [WellFoundedLT W] → SimpleGraph V → (V → W) → Prop :=
fun {V : Type u} {W : Type w} [LinearOrder W] [WellFoundedLT W] (G : SimpleGraph V) (c : V → W) =>
  Nonempty V ∧ G.Preconnected ∧ SeifertStatement.ExchangeStructure G c
structure SeifertApplicationStatement.Outputs.{u} {V : Type u} (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ)
  (x u w p q : V) : Prop
number of parameters: 9
fields:
  SeifertApplicationStatement.Outputs.a_up : SeifertApplicationStatement.EqAdj G p x ∧
      SeifertApplicationStatement.EqAdj G p u ∧ SeifertApplicationStatement.EqAdj G p w
  SeifertApplicationStatement.Outputs.a_down : SeifertApplicationStatement.EqAdj G q x ∧
      SeifertApplicationStatement.EqAdj G q u ∧ SeifertApplicationStatement.EqAdj G q w
  SeifertApplicationStatement.Outputs.b : ∀ (z : V),
      SeifertApplicationStatement.EqAdj G z u →
        SeifertApplicationStatement.EqAdj G z w →
          SeifertApplicationStatement.EqAdj G z p ∧ SeifertApplicationStatement.EqAdj G z q
  SeifertApplicationStatement.Outputs.c : g p + g q ≤ g u + g w
  SeifertApplicationStatement.Outputs.d : g p + g q = g u + g w → A p + A q < A u + A w
constructor:
  SeifertApplicationStatement.Outputs.mk.{u} {V : Type u} {G : SimpleGraph V} {g : V → ℕ} {A : V → ℝ} {x u w p q : V}
    (a_up :
      SeifertApplicationStatement.EqAdj G p x ∧
        SeifertApplicationStatement.EqAdj G p u ∧ SeifertApplicationStatement.EqAdj G p w)
    (a_down :
      SeifertApplicationStatement.EqAdj G q x ∧
        SeifertApplicationStatement.EqAdj G q u ∧ SeifertApplicationStatement.EqAdj G q w)
    (b :
      ∀ (z : V),
        SeifertApplicationStatement.EqAdj G z u →
          SeifertApplicationStatement.EqAdj G z w →
            SeifertApplicationStatement.EqAdj G z p ∧ SeifertApplicationStatement.EqAdj G z q)
    (c : g p + g q ≤ g u + g w) (d : g p + g q = g u + g w → A p + A q < A u + A w) :
    SeifertApplicationStatement.Outputs G g A x u w p q
structure SeifertApplicationStatement.SurfaceSystem.{u} {V : Type u} (G : SimpleGraph V) (g : V → ℕ) (A : V → ℝ) : Prop
number of parameters: 4
fields:
  SeifertApplicationStatement.SurfaceSystem.positive : ∀ (v : V), 0 < A v
  SeifertApplicationStatement.SurfaceSystem.connected : G.Connected
  SeifertApplicationStatement.SurfaceSystem.wellFounded : WellFounded
      fun (x1 x2 : ↑(SeifertApplicationStatement.Values g A)) => x1 < x2
  SeifertApplicationStatement.SurfaceSystem.outputs : ∀ (x u w : V),
      G.Adj x u → G.Adj x w → G.edist u w = 2 → ∃ (p : V) (q : V), SeifertApplicationStatement.Outputs G g A x u w p q
constructor:
  SeifertApplicationStatement.SurfaceSystem.mk.{u} {V : Type u} {G : SimpleGraph V} {g : V → ℕ} {A : V → ℝ}
    (positive : ∀ (v : V), 0 < A v) (connected : G.Connected)
    (wellFounded : WellFounded fun (x1 x2 : ↑(SeifertApplicationStatement.Values g A)) => x1 < x2)
    (outputs :
      ∀ (x u w : V),
        G.Adj x u →
          G.Adj x w → G.edist u w = 2 → ∃ (p : V) (q : V), SeifertApplicationStatement.Outputs G g A x u w p q) :
    SeifertApplicationStatement.SurfaceSystem G g A
def SeifertApplicationStatement.GenusSet.{u} : {V : Type u} → (V → ℕ) → ℕ → Set V :=
fun {V : Type u} (g : V → ℕ) (ℓ : ℕ) => {v : V | g v ≤ ℓ}
def SeifertApplicationStatement.AreaSet.{u} : {V : Type u} → (V → ℕ) → (V → ℝ) → ℕ → ℝ → Set V :=
fun {V : Type u} (g : V → ℕ) (A : V → ℝ) (ℓ : ℕ) (a₀ : ℝ) => {v : V | g v < ℓ ∨ g v = ℓ ∧ A v ≤ a₀}
def SeifertApplicationStatement.FullConclusion.{u} : {V : Type u} → SimpleGraph V → Set V → Prop :=
fun {V : Type u} (G : SimpleGraph V) (D : Set V) =>
  (SimpleGraph.induce D G).Connected ∧
    (∀ (s t : ↑D), (SimpleGraph.induce D G).dist s t = G.dist ↑s ↑t) ∧
      (∀ (s t : ↑D), (SimpleGraph.induce D G).edist s t = G.edist ↑s ↑t) ∧
        ContractibleSpace (SeifertApplicationStatement.FullRealization G D)
```
<!-- END MACHINE TYPES -->
