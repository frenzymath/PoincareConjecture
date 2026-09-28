import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection







open Set
open scoped Manifold ContDiff Bundle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture.RiemannianMetric
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold I' ∞ N]
def productForm (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (h : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : N → Type _)) (x : M × N) :
    TangentSpace (I.prod I') x →L[ℝ]
      TangentSpace (I.prod I') x →L[ℝ] ℝ :=
  Induced.pullbackForm g Prod.fst x + Induced.pullbackForm h Prod.snd x

theorem productForm_apply (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (h : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : N → Type _)) (x : M × N)
    (v w : TangentSpace (I.prod I') x) :
    productForm g h x v w = g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 := by
  simp only [productForm, add_apply,
    Induced.pullbackForm_apply, mfderiv_fst, mfderiv_snd]
  rfl

theorem productForm_pos (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (h : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : N → Type _)) (x : M × N)
    (v : TangentSpace (I.prod I') x) (hv : v ≠ 0) :
    0 < productForm g h x v v := by
  rw [productForm_apply]
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := by intro h2; exact hv (Prod.ext h1 h2)
    simpa only [h1, map_zero, zero_apply, zero_add] using h.pos x.2 v.2 h2
  · have hn : 0 ≤ h.inner x.2 v.2 v.2 := by
      by_cases h2 : v.2 = 0
      · simp [h2]
      · exact (h.pos x.2 v.2 h2).le
    exact add_pos_of_pos_of_nonneg (g.pos x.1 v.1 h1) hn

theorem productForm_contMDiff (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (h : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : N → Type _)) :
    ContMDiff (I.prod I')
      ((I.prod I').prod 𝓘(ℝ,
        (E × E') →L[ℝ]
        (E × E') →L[ℝ] ℝ)) ∞
      (fun x => (⟨x, productForm g h x⟩ : Bundle.TotalSpace
        ((E × E') →L[ℝ]
        (E × E') →L[ℝ] ℝ)
        (fun x : M × N => TangentSpace (I.prod I') x →L[ℝ]
          TangentSpace (I.prod I') x →L[ℝ] ℝ))) :=
  (Induced.pullbackForm_contMDiff (I := I.prod I') g contMDiff_fst).add_section
    (Induced.pullbackForm_contMDiff (I := I.prod I') h contMDiff_snd)

def product (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (h : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : N → Type _)) :
    Bundle.ContMDiffRiemannianMetric (I.prod I') ∞
      (E × E')
      (TangentSpace (I.prod I') : M × N → Type _) where
  inner := productForm g h
  symm x v w := by rw [productForm_apply, productForm_apply, g.symm, h.symm]
  pos := productForm_pos g h
  isVonNBounded x := by
    obtain ⟨A, hA⟩ := (NormedSpace.isVonNBounded_iff' ℝ (E := E)).mp (g.isVonNBounded x.1)
    obtain ⟨B, hB⟩ := (NormedSpace.isVonNBounded_iff' ℝ (E := E')).mp (h.isVonNBounded x.2)
    apply (NormedSpace.isVonNBounded_iff' ℝ
      (E := E × E')).mpr
    refine ⟨max A B, ?_⟩
    intro v hv
    have gn : 0 ≤ g.inner x.1 v.1 v.1 := by
      by_cases hz : v.1 = 0
      · simp [hz]
      · exact (g.pos x.1 v.1 hz).le
    have hn : 0 ≤ h.inner x.2 v.2 v.2 := by
      by_cases hz : v.2 = 0
      · simp [hz]
      · exact (h.pos x.2 v.2 hz).le
    change productForm g h x v v < 1 at hv
    rw [productForm_apply] at hv
    exact max_le_max (hA v.1 (by change g.inner x.1 v.1 v.1 < 1; linarith))
      (hB v.2 (by change h.inner x.2 v.2 v.2 < 1; linarith))
  contMDiff := productForm_contMDiff g h

@[simp] theorem product_inner (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (h : Bundle.ContMDiffRiemannianMetric I' ∞ E' (TangentSpace I' : N → Type _)) (x : M × N)
    (v w : TangentSpace (I.prod I') x) :
    (product g h).inner x v w = g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 :=
  productForm_apply g h x v w
end PoincareConjecture.RiemannianMetric
