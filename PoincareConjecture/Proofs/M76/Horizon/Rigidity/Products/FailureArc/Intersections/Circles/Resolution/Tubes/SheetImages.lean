import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SourceBranches

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem identity_tube_source_image_iff
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {S : Set P2} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index} {L d : ℝ}
    (T : ComponentIdentityAnnuliData (e := e) (R := R) old i L d)
    (j : Fin 2) (z : P2 × ℝ) (hz : z ∈ _root_.Dehn.identityTube L d) :
    T.tube z ∈ f '' T.source j ↔ z.1.2 = if j = 0 then z.1.1 else -z.1.1 := by
  have hd := T.depth_pos
  have hw := T.width_small
  have hdiag (u : Icc (-d) d) (s : ℝ) (hs : s ∈ Icc 0 (4 * L)) :
      (sourceTubeDiagonal j u,s) ∈ _root_.Dehn.identityTube L d := by
    refine ⟨⟨u.property,?_⟩,hs⟩
    change (if j = 0 then (u : ℝ) else -(u : ℝ)) ∈ Icc (-d) d
    split_ifs <;> constructor <;> linarith [u.property.1,u.property.2]
  constructor
  · rintro ⟨x,hx,hxz⟩
    let p := (T.chart j).symm ⟨x,hx⟩
    have hpx : (T.chart j p : P2) = x := congrArg Subtype.val ((T.chart j).apply_symm_apply _)
    obtain ⟨s,hs,hsp⟩ := exists_period_parameter_of_depth hd hw p
    let u : Icc (-d) d := ⟨depth L p,(mem_squareAnnulus_iff_depth.mp p.property)⟩
    have hvalue := T.period_value j s hs u
    have hpeq : (⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)),u),
        _root_.Dehn.annulus_period_point_mem hd hw _ u⟩ : squareAnnulus L d) = p :=
      Subtype.ext hsp.symm
    rw [hpeq,hpx,hxz] at hvalue
    have heq := ((T.tube_fibers z hz _ (hdiag u s hs)).mp hvalue).1
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    change z.1.1 = (u : ℝ) at hfst
    change z.1.2 = if j = 0 then (u : ℝ) else -(u : ℝ) at hsnd
    rwa [← hfst] at hsnd
  · intro hzdiag
    let u : Icc (-d) d := ⟨z.1.1,hz.1.1⟩
    let p : squareAnnulus L d := ⟨annulusMap L (by linarith)
      ((z.2 : AddCircle (4 * L)),u),_root_.Dehn.annulus_period_point_mem hd hw _ u⟩
    refine ⟨T.chart j p,(T.chart j p).property,?_⟩
    have hvalue := T.period_value j z.2 hz.2 u
    have hcoord : (sourceTubeDiagonal j u,z.2) = z := by
      refine Prod.ext ?_ rfl
      exact Prod.ext rfl hzdiag.symm
    exact hvalue.trans (congrArg T.tube hcoord)

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
