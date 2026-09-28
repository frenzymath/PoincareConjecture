import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.AtlasOfCover

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E F ι : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem compatible_of_piecewiseAffine_cover
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    (H H' : OpenPartialHomeomorph M E)
    (hH : ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E)
    (hH' : ∀ i, (e i).symm.trans H' ∈ piecewiseAffineGroupoid E) :
    H.symm.trans H' ∈ piecewiseAffineGroupoid E := by
  letI := ChartedSpace.ofChartCover e hcover
  letI : HasGroupoid M (piecewiseAffineGroupoid E) :=
    ChartedSpace.hasGroupoid_ofChartCover e hcover _ hcompat
  have hmem (T : OpenPartialHomeomorph M E)
      (hT : ∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid E) :
      T ∈ (piecewiseAffineGroupoid E).maximalAtlas M := by
    rintro _ ⟨i, rfl⟩
    refine ⟨?_, hT i⟩
    simpa only [trans_symm_eq_symm_trans_symm, symm_symm] using
      (piecewiseAffineGroupoid E).symm (hT i)
  exact (piecewiseAffineGroupoid E).compatible_of_mem_maximalAtlas (hmem H hH) (hmem H' hH')

theorem exists_piecewiseAffine_hypersurface_cover
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {B : Set M} (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (hhyp : ∀ x ∈ B,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (H : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ H.source ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E) ∧
        H.IsImage B {z | ell z = 0}) :
    ∃ q : B → OpenPartialHomeomorph B F,
      (∀ x : B, x ∈ (q x).source) ∧
      ∀ x y : B, (q x).symm.trans (q y) ∈ piecewiseAffineGroupoid F := by
  classical
  choose ell v H hv hx hH himage using fun x : B => hhyp x x.property
  have hcoords (x : B) :
      ∃ (a : F →ᴬ[ℝ] E) (r : E →ᴬ[ℝ] F),
        Function.LeftInverse r a ∧ LeftInvOn a r {z | ell x z = 0} ∧
        ∀ z, ell x (a z) = 0 := by
    have hnonzero : (ell x).toAffineMap.linear ≠ 0 := by
      intro hzero
      have hvalue : (ell x).toAffineMap.linear (v x) = 1 := hv x
      rw [hzero, LinearMap.zero_apply] at hvalue
      exact zero_ne_one hvalue
    exact (ell x).toAffineMap.exists_zeroLevel_coordinates hnonzero hdim
  choose a r hra har haz using hcoords
  choose q hsource htarget hforward hinverse using fun x : B =>
    (H x).exists_affine_hypersurface_chart (ell x) (himage x)
      (a x) (r x) (hra x) (har x) (haz x) x
  refine ⟨q, ?_, ?_⟩
  · intro x
    rw [hsource x]
    exact hx x
  · intro x y
    exact affine_hypersurface_transition_mem (H x) (H y) (q x) (q y) (a x) (r y)
      (hsource y) (htarget x) (hforward y) (hinverse x)
      (compatible_of_piecewiseAffine_cover e hcompat hcover (H x) (H y) (hH x) (hH y))

theorem exists_piecewiseAffine_hypersurface_chartedSpace
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {B : Set M} (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (hhyp : ∀ x ∈ B,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (H : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ H.source ∧
        (∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid E) ∧
        H.IsImage B {z | ell z = 0}) :
    ∃ c : ChartedSpace F B, letI := c; HasGroupoid B (piecewiseAffineGroupoid F) := by
  obtain ⟨q, hq, hPL⟩ := exists_piecewiseAffine_hypersurface_cover e hcompat hcover hdim hhyp
  let hqcover : ∀ x : B, ∃ y, x ∈ (q y).source := fun x => ⟨x, hq x⟩
  exact ⟨ChartedSpace.ofChartCover q hqcover,
    ChartedSpace.hasGroupoid_ofChartCover q hqcover _ hPL⟩

end OpenPartialHomeomorph
