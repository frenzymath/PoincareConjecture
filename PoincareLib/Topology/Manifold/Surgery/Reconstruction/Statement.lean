import PoincareLib.Topology.Manifold.ConnectedSum.Reconstruction

/-!
# M72 finite reconstruction statement

Natural-language theorem statement: given one actual M52 changing-carrier
global-flow package, its M71 finite-extinction conclusion tied to the raw
vanishing event, the original connectedness, and a same-flow M38 topology
service, reverse the finite surgery history.  M52 supplies local finiteness. The
conclusion must first produce the exact finite surgery ledger, then index every
summand by an actual non-survivor piece of an event's local
`SurgeryTopologyConclusion`, and finally construct the global
`SmoothFiniteConnectedSumAssembly` of the time-zero flow slice.  Each survivor
must be transported by an immediate-successor record that includes the
regular-slab diffeomorphism, its component image, and a componentwise
region equivalence; the later event's own local reconstruction is then used
for the assembly substitution.

M72 does not accept an assembly, a free list of pieces, a sphere
identification, a factor classification, or either Poincare theorem.  Its
single admission owns the finite reverse-time induction, survivor transport,
component substitutions through regular slabs, and composition of the local
reconstruction witnesses.

Source: Morgan--Tian Proposition 15.3 and Corollary 15.4, printed
pp. 357--359, `references/derived/MT2007.txt:17814-17902`; the finite surgery
process is the Section 15.4 discussion.  M38 supplies the local topology
records through the calibrated raw-flow provider. M72 constructs the finite
ledger from M52's local finiteness and constructs immediate-successor chronology
inside that ledger; M71 supplies the selected empty surgery time, whose
terminal vanishing event is derived from the raw flow.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

def M72FiniteReconstructionStatement : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N),
    Nonempty (M72ReconstructionConclusion I)

end PoincareMT
