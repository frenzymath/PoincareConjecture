import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnitCubePLCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finitePL_ball_inward_collar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {B Q : Set E} (hB : IsFinitePLBallPair V3 B Q) :
    ∃ C : E × ℝ → E, FinitePiecewiseAffineOn C (Q ×ˢ Icc (0 : ℝ) 1) ∧
      InjOn C (Q ×ˢ Icc (0 : ℝ) 1) ∧ MapsTo C (Q ×ˢ Icc (0 : ℝ) 1) B ∧
      (∀ x ∈ Q, C (x, 0) = x) ∧
      ∀ z ∈ Q ×ˢ Icc (0 : ℝ) 1, C z ∈ Q ↔ z.2 = 0 := by
  classical
  obtain ⟨H, hH, hHrim⟩ := hB.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  have hHcopy := hH
  obtain ⟨f, hf, hfval⟩ := hHcopy
  obtain ⟨g, hg, hgval⟩ := hH.symm
  have hgf : LeftInvOn g f B := by
    intro x hx
    rw [← hfval ⟨x, hx⟩, ← hgval, H.symm_apply_apply]
  have hfg : LeftInvOn f g (closedBall (0 : V3) 1) := by
    intro x hx
    rw [← hgval ⟨x, hx⟩, ← hfval, H.apply_symm_apply]
  have hfQ {x : E} (hx : x ∈ Q) : f x ∈ sphere (0 : V3) 1 := by
    have hh := (hHrim ⟨x, hB.1 hx⟩).mp hx
    rw [hfval, frontier_closedBall _ one_ne_zero] at hh
    exact hh
  have hgB {y : V3} (hy : y ∈ closedBall (0 : V3) 1) : g y ∈ B := by
    rw [← hgval ⟨y, hy⟩]
    exact (H.symm ⟨y, hy⟩).property
  have hgQ {y : V3} (hy : y ∈ closedBall (0 : V3) 1) : g y ∈ Q ↔ ‖y‖ = 1 := by
    have hh := hHrim (H.symm ⟨y, hy⟩)
    rw [H.apply_symm_apply, hgval, frontier_closedBall _ one_ne_zero,
      mem_sphere_zero_iff_norm] at hh
    exact hh
  obtain ⟨U, hU, huval, hunorm, huzero⟩ := exists_unitCube_inward_finitePL_collar
  obtain ⟨u, hu, huval'⟩ := hU
  have hueq (z : (sphere (0 : V3) 1 ×ˢ Icc (0 : ℝ) (1 / 8))) :
      u z = (U z : V3) := (huval' z).symm
  obtain ⟨_, L, _, _, hL, hLQ⟩ := hB.exists_finite_carrier_and_rim_complexes
  obtain ⟨J, _, hJ, hJI, _, _⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).exists_finite_carrier_and_rim_complexes
  obtain ⟨T, hT, hTs, _⟩ := L.exists_finite_triangulation_prod J hL hJ
  have hTQ : T.space = Q ×ˢ Icc (0 : ℝ) 1 := by simpa only [hLQ, hJI] using hTs
  have hfst : FinitePiecewiseAffineOn (Prod.fst : E × ℝ → E) T.space :=
    ⟨T, hT, rfl, T.affineOnFaces_affine (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap⟩
  have hfT : FinitePiecewiseAffineOn (fun z : E × ℝ => f z.1) T.space :=
    hf.comp hfst (fun z hz => hB.1 (hTQ.subset hz).1)
  let depth : E × ℝ →ᴬ[ℝ] ℝ := (1 / 8 : ℝ) •
    (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap
  have htPL : FinitePiecewiseAffineOn (fun z : E × ℝ => z.2 / 8) T.space := by
    apply ((T.affineOnFaces_affine depth).finitePiecewiseAffineOn hT).congr
    intro z _
    change (1 / 8 : ℝ) * z.2 = z.2 / 8
    ring
  let a : E × ℝ → V3 × ℝ := fun z => (f z.1, z.2 / 8)
  have ha : FinitePiecewiseAffineOn a (Q ×ˢ Icc (0 : ℝ) 1) := hTQ ▸ hfT.prod_mk htPL
  have hamap : MapsTo a (Q ×ˢ Icc (0 : ℝ) 1)
      (sphere (0 : V3) 1 ×ˢ Icc (0 : ℝ) (1 / 8)) := by
    intro z hz
    exact ⟨hfQ hz.1, by dsimp [a]; constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have huB (z : E × ℝ) (hz : z ∈ Q ×ˢ Icc (0 : ℝ) 1) :
      u (a z) ∈ closedBall (0 : V3) 1 := by
    rw [hueq ⟨a z, hamap hz⟩, mem_closedBall_zero_iff]
    exact (U ⟨a z, hamap hz⟩).property.2
  let C := g ∘ u ∘ a
  have hC : FinitePiecewiseAffineOn C (Q ×ˢ Icc (0 : ℝ) 1) :=
    hg.comp (hu.comp ha hamap) (fun z hz => huB z hz)
  have hCi : InjOn C (Q ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz w hw hzw
    have hh := hfg.injOn (huB z hz) (huB w hw) hzw
    rw [hueq ⟨a z, hamap hz⟩, hueq ⟨a w, hamap hw⟩] at hh
    have haa := congrArg Subtype.val (U.injective (Subtype.ext hh))
    have hfirst := hgf.injOn (hB.1 hz.1) (hB.1 hw.1) (congrArg Prod.fst haa)
    have hsecond : z.2 = w.2 := by
      have h := congrArg Prod.snd haa
      change z.2 / 8 = w.2 / 8 at h
      linarith
    exact Prod.ext hfirst hsecond
  refine ⟨C, hC, hCi, fun z hz => hgB (huB z hz), ?_, ?_⟩
  · intro x hx
    have hz : (x, (0 : ℝ)) ∈ Q ×ˢ Icc (0 : ℝ) 1 := ⟨hx, by simp⟩
    change g (u (a (x, 0))) = x
    rw [hueq ⟨a (x, 0), hamap hz⟩, huzero _ (by simp [a])]
    exact hgf (hB.1 hx)
  · intro z hz
    change g (u (a z)) ∈ Q ↔ z.2 = 0
    rw [hgQ (huB z hz), hueq ⟨a z, hamap hz⟩, hunorm]
    change 1 - z.2 / 8 = 1 ↔ z.2 = 0
    constructor <;> intro h <;> linarith

end PoincareConjecture.M76
