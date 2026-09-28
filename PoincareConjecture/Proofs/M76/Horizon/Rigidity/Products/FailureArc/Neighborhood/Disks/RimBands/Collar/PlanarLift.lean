import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.OriginalLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.RimCoordinates

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands
open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem IntervalBandLift.exists_arm_chart_width
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    {P : OriginalDiskProduct e Q j} {F : P2 → X} {b : Bool}
    (L : IntervalBandLift P F (rimArm b)) :
    ∃ w : ℝ, 0 < w ∧ w ≤ L.width ∧
      ∀ p ∈ parameter w, 0 < sign b * (L.coordinates p).1 0 := by
  let f : J × I → E := fun z => L.coordinates (L.width * (z.2 : ℝ),(z.1 : ℝ))
  have hf : Continuous f := L.finitePL.continuousOn.comp_continuous
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp continuous_fst)) (by
        intro z
        refine ⟨?_,z.1.property⟩
        constructor <;> nlinarith [z.2.property.1,z.2.property.2,L.positive])
  let O : Set E := {z | 0 < sign b * z.1 0}
  have hO : IsOpen O := isOpen_lt continuous_const
    (continuous_const.mul ((continuous_apply 0).comp continuous_fst))
  have hbase (t : J) : f (t,⟨0,by norm_num⟩) ∈ O := by
    change 0 < sign b * (L.coordinates (L.width*0,(t : ℝ))).1 0
    rw [mul_zero,L.center t t.property]
    cases b <;> norm_num [rimArm,sign]
  let : CompactSpace J := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨a,ha,hasmall,hthin⟩ := hf.exists_closed_strip_subset hO hbase
  refine ⟨L.width*a,mul_pos L.positive ha,?_,?_⟩
  · nlinarith [L.positive]
  · intro p hp
    have hpa : p.1 / L.width ∈ Icc (-a) a := by
      constructor
      · apply (le_div_iff₀ L.positive).mpr
        nlinarith [hp.1.1]
      · apply (div_le_iff₀ L.positive).mpr
        nlinarith [hp.1.2]
    have hpI : p.1 / L.width ∈ I := by
      constructor <;> linarith [hpa.1,hpa.2]
    have hh := hthin ⟨p.2,hp.2⟩ ⟨p.1/L.width,hpI⟩ (abs_le.mpr hpa)
    change 0 < sign b * (L.coordinates (L.width*(p.1/L.width),p.2)).1 0 at hh
    simpa [mul_div_cancel₀ _ L.positive.ne'] using hh

theorem IntervalBandLift.exists_planar_arm_lift
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}
    {P : OriginalDiskProduct e Q j} {F : P2 → X} {b : Bool}
    (L : IntervalBandLift P F (rimArm b)) :
    ∃ (w : ℝ) (g : P2 → P2), 0 < w ∧ w ≤ L.width ∧
      FinitePiecewiseAffineOn g (parameter w) ∧ InjOn g (parameter w) ∧
      MapsTo g (parameter w) (Ioo (-(1/2 : ℝ)) (3/2) ×ˢ Ioo (-(1/2 : ℝ)) (1/2)) ∧
      (∀ t ∈ J, g (0,t) = (t,0)) ∧
      (∀ p ∈ parameter w, P.map (armPoint b (g p).1,(g p).2) = F p) ∧
      (∀ p ∈ parameter w, (g p).2=0 ↔ p.1=0) := by
  obtain ⟨w,hw,hwL,hchart⟩ := L.exists_arm_chart_width
  have hsub : parameter w ⊆ parameter L.width := fun p hp =>
    ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,hp.2⟩
  have hball := (isFinitePLBallPair_Icc (by linarith : -w < w)).prod
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
  have hq : FinitePiecewiseAffineOn L.coordinates (parameter w) := by
    simpa only [hKs,parameter] using L.finitePL.restrict K hK (hKs.subset.trans hsub)
  let g : P2 → P2 := fun p => (armPhase b (L.coordinates p).1,(L.coordinates p).2)
  have hg : FinitePiecewiseAffineOn g (parameter w) :=
    (finitePL_armPhase (hq.postcomp (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap) b).prod_mk
      (hq.postcomp (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)
  have hback (p : P2) (hp : p ∈ parameter w) :
      (armPoint b (g p).1,(g p).2) = L.coordinates p :=
    Prod.ext (armPoint_armPhase b (L.mapsTo (hsub hp)).1 (hchart p hp)) rfl
  refine ⟨w,g,hw,hwL,hg,?_,?_,?_,?_,?_⟩
  · intro p hp q hq heq
    apply L.injective (hsub hp) (hsub hq)
    exact (hback p hp).symm.trans ((congrArg (fun z : P2 => (armPoint b z.1,z.2)) heq).trans
      (hback q hq))
  · intro p hp
    exact ⟨armPhase_mem b (L.mapsTo (hsub hp)).1 (hchart p hp),(L.mapsTo (hsub hp)).2⟩
  · intro t ht
    dsimp [g]
    rw [L.center t ht]
    exact Prod.ext (armPhase_rimArm b ht) rfl
  · intro p hp
    rw [hback p hp]
    exact L.physical p (hsub hp)
  · intro p hp
    exact L.zero_iff p (hsub hp)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
