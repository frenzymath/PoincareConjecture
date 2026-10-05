import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.PersistenceGeometry

/-!
# A shared tolerance for the actual cap comparison

Increasing the tolerance truncates the frozen full covariant jet sum
and retains its original strict uniform witness. Proposition 16.5,
p. 370; canonical-neck-cap-included.md, Stage A.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.Proofs.M47

/-- The recorded full metric error decreases when its order is truncated. -/
theorem singularMetricJetErrorSquared_mono_order
    {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 X) (D : LeviCivitaData g)
    (B : CovariantTensorEvaluation 3 X 2) {k m : ℕ} (hkm : k ≤ m) (x : X) :
    singularMetricJetErrorSquared g D B k x ≤
      singularMetricJetErrorSquared g D B m x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hkm 1))
  intro j _ _
  exact sq_nonneg _

/-- The same actual cap comparison satisfies every larger positive
tolerance, with its original lifetime, chart image and uniform witness. -/
theorem capFamilyComparison_mono_tolerance
    {F : SurgeryFlowData.{u}} {S : MaximalStandardCapFlow F.standard_initial}
    {A eta eta' t : ℝ} {I : Set ℝ} {U : Set (F.slice t).carrier}
    {e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U}
    {chart : StandardCapSpace → (F.slice t).carrier}
    (heta : 0 < eta) (hle : eta ≤ eta')
    (hcompare : SurgeryCapFamilyComparison F S A eta e chart) :
    SurgeryCapFamilyComparison F S A eta' e chart := by
  obtain ⟨b, hb, hlifetime, htime, himage, hjets⟩ := hcompare
  have horder : ⌊eta'⁻¹⌋₊ ≤ ⌊eta⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ (heta.trans_le hle) heta).mpr hle)
  refine ⟨b, hb.trans_le (pow_le_pow_left₀ heta.le hle 2),
    hlifetime, htime, himage, ?_⟩
  intro s hs x hx
  exact (singularMetricJetErrorSquared_mono_order (S.metric s) (S.connection s)
    _ horder x).trans (hjets s hs x hx)

end PoincareMT.Proofs.M47
