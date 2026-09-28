import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.TranslatedSquare
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.Order.Floor.Ring
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralPLDiskExtension



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.finitePiecewiseAffineOn_periodic_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K) (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z : Square p, h (projection p z) = M.map z)
    (J : SimplicialComplex ℝ P2) (hJ : J.faces.Finite) :
    FinitePiecewiseAffineOn
      (fun z : P2 => (h ((z.1 : AddCircle p), (z.2 : AddCircle p)) : E)) J.space := by
  classical
  have hp : 0 < p := Fact.out
  obtain ⟨u, hu, huv⟩ := M.finite_piecewise_affine
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (J.isCompact_space_of_finite hJ).isBounded
  let I : Set ℤ := Icc ⌊-B / p⌋ ⌊B / p⌋
  let σ := I × I
  let shift (n : σ) : P2 := ((n.1 : ℤ) * p, (n.2 : ℤ) * p)
  let tr (n : σ) : P2 ≃ᴬ[ℝ] P2 := ContinuousAffineEquiv.constVAdd ℝ P2 (-shift n)
  let T (n : σ) : Set P2 := (tr n).symm '' squareCarrier p
  have hperiod (n : ℤ) (x : ℝ) : ((x - n * p : ℝ) : AddCircle p) = (x : AddCircle p) := by
    rw [AddCircle.coe_sub, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, sub_zero]
  have hpiece (n : σ) : FinitePiecewiseAffineOn
      (fun z : P2 => (h ((z.1 : AddCircle p), (z.2 : AddCircle p)) : E)) (T n) := by
    apply (hu.precomp_affineEquiv (tr n)).congr
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    have htx : tr n ((tr n).symm x) = x := (tr n).apply_symm_apply x
    change u (tr n ((tr n).symm x)) = _
    rw [htx, huv (⟨x.1, hx.1⟩, ⟨x.2, hx.2⟩), ← hh]
    change (h ((x.1 : AddCircle p), (x.2 : AddCircle p)) : E) = _
    have hcoords : (tr n).symm x = (x.1 + (n.1 : ℤ) * p, x.2 + (n.2 : ℤ) * p) := by
      change -(-shift n) + x = _
      rw [neg_neg]
      ext <;> dsimp [shift] <;> ring
    rw [hcoords]
    apply congrArg (fun z => (h z : E))
    apply Prod.ext
    · have hp' := hperiod (n.1 : ℤ) (x.1 + (n.1 : ℤ) * p)
      simpa only [add_sub_cancel_right] using hp'
    · have hp' := hperiod (n.2 : ℤ) (x.2 + (n.2 : ℤ) * p)
      simpa only [add_sub_cancel_right] using hp'
  have hcover : J.space ⊆ ⋃ n : σ, T n := by
    intro z hz
    have hnorm := hB z hz
    have hx : -B ≤ z.1 ∧ z.1 ≤ B := abs_le.mp
      ((show |z.1| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_fst_le z).trans hnorm)
    have hy : -B ≤ z.2 ∧ z.2 ≤ B := abs_le.mp
      ((show |z.2| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_snd_le z).trans hnorm)
    have hn {x : ℝ} (hx : -B ≤ x ∧ x ≤ B) : ⌊x / p⌋ ∈ I :=
      ⟨Int.floor_mono ((div_le_div_iff_of_pos_right hp).mpr hx.1),
        Int.floor_mono ((div_le_div_iff_of_pos_right hp).mpr hx.2)⟩
    let n : σ := (⟨⌊z.1 / p⌋, hn hx⟩, ⟨⌊z.2 / p⌋, hn hy⟩)
    have htile (x : ℝ) : x - ⌊x / p⌋ * p ∈ Icc (0 : ℝ) p := by
      have hl := (le_div_iff₀ hp).mp (Int.floor_le (x / p))
      have hu := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one (x / p))
      constructor <;> linarith
    have htz : tr n z ∈ squareCarrier p := by
      change (-( ((⌊z.1 / p⌋ : ℤ) : ℝ) * p) + z.1 ∈ Icc (0 : ℝ) p) ∧
        (-( ((⌊z.2 / p⌋ : ℤ) : ℝ) * p) + z.2 ∈ Icc (0 : ℝ) p)
      constructor
      · convert htile z.1 using 1; ring
      · convert htile z.2 using 1; ring
    exact mem_iUnion.mpr ⟨n, tr n z, htz, (tr n).symm_apply_apply z⟩
  exact (FinitePiecewiseAffineOn.iUnion hpiece).restrict J hJ hcover

theorem SourceSquareMap.finitePiecewiseAffineOn_periodic_comp
    {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E}
    (M : SourceSquareMap p K) (h : (AddCircle p × AddCircle p) ≃ₜ K.space)
    (hh : ∀ z : Square p, h (projection p z) = M.map z)
    {A : Set Z} {r : Z → P2} (hr : FinitePiecewiseAffineOn r A) :
    FinitePiecewiseAffineOn
      (fun z : Z => (h (((r z).1 : AddCircle p), ((r z).2 : AddCircle p)) : E)) A := by
  obtain ⟨J, hJ, hJs⟩ := hr.exists_finite_triangulation_image
  exact (M.finitePiecewiseAffineOn_periodic_coordinates h hh J hJ).comp hr
    (fun x hx => hJs.symm.subset ⟨x, hx, rfl⟩)

theorem SourceSquareMap.polyhedralPL_periodic_comp
    {E Z V X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V}
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S : Set X}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z))
    (J : SimplicialComplex ℝ Z) (hJ : J.faces.Finite)
    {r : Z → P2} (hr : FinitePiecewiseAffineOn r J.space) :
    PolyhedralPLInCharts e
      (fun z : Z => (h (((r z).1 : AddCircle p), ((r z).2 : AddCircle p)) : X)) J.space := by
  let k := h.trans H.symm
  have hk (z : Square p) : k (projection p z) = M.map z := by
    change H.symm (h (projection p z)) = M.map z
    rw [hvalue, H.symm_apply_apply]
  have hm := M.finitePiecewiseAffineOn_periodic_comp k hk hr
  have hcomp := hF.comp_finitePiecewiseAffineOn J hJ hm (fun z _ => (k _).property)
  apply hcomp.congr
  intro z _
  change F (k _) = _
  rw [hFval]
  exact congrArg Subtype.val (H.apply_symm_apply _)

end PoincareConjecture.M76.PeriodicSquare
