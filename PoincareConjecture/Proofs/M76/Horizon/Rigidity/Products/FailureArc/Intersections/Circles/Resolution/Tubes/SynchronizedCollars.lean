import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SheetSwap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.MiddleDisk



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => (P2 × ℝ)

structure SynchronizedCircleCollars
    {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (f₀ f₁ : P2 → X)
    (S₀ S₁ C₀ C₁ : Set P2) (R : Set X) (L d : ℝ) where
  depth_pos : 0 < d
  width_small : 4 * d < L
  source₀ : Set P2
  source₁ : Set P2
  collar₀ : OrientedPolygonCollar L d source₀
  collar₁ : OrientedPolygonCollar L d source₁
  tube : C3 → X
  tube_PL : PolyhedralPLInCharts e tube (identityTube L d)
  tube_interior : MapsTo tube (identityTube L d) (interior R)
  tube_fibers : ∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
    tube z = tube w ↔ z.1 = w.1 ∧
      (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))
  source₀_subset : source₀ ⊆ interior S₀
  source₁_subset : source₁ ⊆ interior S₁
  middle₀ : (fun p : squareAnnulus L d => (collar₀.chart p : P2)) ''
    {p | depth L p = 0} = C₀
  middle₁ : (fun p : squareAnnulus L d => (collar₁.chart p : P2)) ''
    {p | depth L p = 0} = C₁
  whole₀ : ∀ z ∈ identityTube L d, tube z ∈ f₀ '' S₀ ↔ z.1.2 = -z.1.1
  whole₁ : ∀ z ∈ identityTube L d, tube z ∈ f₁ '' S₁ ↔ z.1.2 = z.1.1
  period₀ : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d)
    (p : squareAnnulus L d), (p : P2) =
      annulusMap L (by linarith [depth_pos,width_small]) ((s : AddCircle (4 * L)),u) →
      f₀ (collar₀.chart p) = tube ((u,-u),s)
  period₁ : ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d)
    (p : squareAnnulus L d), (p : P2) =
      annulusMap L (by linarith [depth_pos,width_small]) ((s : AddCircle (4 * L)),u) →
      f₁ (collar₁.chart p) = tube ((u,u),s)

theorem SeparatedCircleSource.nonempty_synchronizedCollars
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f₀ f₁ : P2 → X}
    {S₀ S₁ C₀ C₁ : Set P2} {R : Set X}
    (D : SeparatedCircleSource e f₀ f₁ S₀ S₁ C₀ C₁ R)
    {i : D.decomposition.Index} {L d : ℝ}
    (T : ComponentIdentityAnnuliData (e := e) (R := R) D.decomposition i L d)
    (hi : D.decomposition.pieces i = C₀)
    (hmi : D.decomposition.pieces (D.decomposition.mate i) = D.shift '' C₁)
    (hwhole₀ : ∀ z ∈ T.tube '' identityTube L d, z ∈ f₀ '' S₀ ↔ z ∈ f₀ '' D.first.space)
    (hwhole₁ : ∀ z ∈ T.tube '' identityTube L d, z ∈ f₁ '' S₁ ↔ z ∈ f₁ '' D.second.space) :
    Nonempty (SynchronizedCircleCollars e f₀ f₁ S₀ S₁ C₀ C₁ R L d) := by
  classical
  obtain ⟨A,B,τ,hτ,hτR,hfib,hsub,hmid,hwhole,hperiod⟩ :=
    D.exists_original_oriented_collars T hi hmi hwhole₀ hwhole₁
  by_cases hzero : T.label 0 = 0
  · have hone : T.label 1 = 1 := by
      have hh := T.label.injective.ne (show (1 : Fin 2) ≠ 0 by decide)
      rw [hzero] at hh
      exact Fin.eq_one_of_ne_zero _ hh
    obtain ⟨hPL,_,hF⟩ := circleSheetSwap_map e
      (by linarith [T.depth_pos,T.width_small]) T.depth_pos τ hτ hfib
    refine ⟨{
      depth_pos := T.depth_pos, width_small := T.width_small
      source₀ := A 0, source₁ := A 1, collar₀ := B 0, collar₁ := B 1
      tube := τ ∘ circleSheetSwap, tube_PL := hPL
      tube_interior := fun z hz => hτR ((circleSheetSwap_mem L d z).mpr hz)
      tube_fibers := hF
      source₀_subset := by simpa [hzero] using hsub 0
      source₁_subset := by simpa only [hone,show (1 : Fin 2) ≠ 0 by decide,if_false] using hsub 1
      middle₀ := by simpa [hzero] using hmid 0
      middle₁ := by simpa only [hone,show (1 : Fin 2) ≠ 0 by decide,if_false] using hmid 1
      whole₀ := ?_, whole₁ := ?_, period₀ := ?_, period₁ := ?_ }⟩
    · intro z hz
      have hh := hwhole 0 (circleSheetSwap z) ((circleSheetSwap_mem L d z).mpr hz)
      simp only [hzero,ite_true,circleSheetSwap_apply] at hh
      change τ (circleSheetSwap z) ∈ f₀ '' S₀ ↔ _
      exact hh.trans neg_eq_iff_eq_neg
    · intro z hz
      have hh := hwhole 1 (circleSheetSwap z) ((circleSheetSwap_mem L d z).mpr hz)
      simp only [hone,show (1 : Fin 2) ≠ 0 by decide,if_false,circleSheetSwap_apply,neg_inj] at hh
      exact hh
    · intro s hs u p hp
      have hh := hperiod 0 s hs u p hp
      simpa [hzero,sourceTubeDiagonal,circleSheetSwap_apply] using hh
    · intro s hs u p hp
      have hh := hperiod 1 s hs u p hp
      simpa only [hone,show (1 : Fin 2) ≠ 0 by decide,if_false,sourceTubeDiagonal,
        Function.comp_apply,circleSheetSwap_apply] using hh
  · have hzero' : T.label 0 = 1 := Fin.eq_one_of_ne_zero _ hzero
    have hone : T.label 1 = 0 := by
      have hh := T.label.injective.ne (show (1 : Fin 2) ≠ 0 by decide)
      rw [hzero'] at hh
      by_contra h
      exact hh (Fin.eq_one_of_ne_zero _ h)
    refine ⟨{
      depth_pos := T.depth_pos, width_small := T.width_small
      source₀ := A 1, source₁ := A 0, collar₀ := B 1, collar₁ := B 0
      tube := τ, tube_PL := hτ, tube_interior := hτR, tube_fibers := hfib
      source₀_subset := by simpa [hone] using hsub 1
      source₁_subset := by simpa only [hzero,if_false] using hsub 0
      middle₀ := by simpa [hone] using hmid 1
      middle₁ := by simpa only [hzero,if_false] using hmid 0
      whole₀ := ?_, whole₁ := ?_, period₀ := ?_, period₁ := ?_ }⟩
    · intro z hz
      simpa [hone] using hwhole 1 z hz
    · intro z hz
      simpa [hzero] using hwhole 0 z hz
    · intro s hs u p hp
      simpa [hone,sourceTubeDiagonal]
        using hperiod 1 s hs u p hp
    · intro s hs u p hp
      simpa [hzero,sourceTubeDiagonal] using hperiod 0 s hs u p hp

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
