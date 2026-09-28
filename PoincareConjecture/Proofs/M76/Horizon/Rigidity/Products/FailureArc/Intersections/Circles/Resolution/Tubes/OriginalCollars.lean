import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.OriginalSourceCharts
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.OriginalPairOrientation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.WholeSheets

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => (P2 × ℝ)

theorem pairedArmReindex_sheet_iff (r₀ r₁ : Bool) (j : Fin 2) (z : P2) :
    (pairedArmReindex r₀ r₁ z).2 =
      (if j = 0 then (pairedArmReindex r₀ r₁ z).1 else -(pairedArmReindex r₀ r₁ z).1) ↔
      z.2 = (if j = 0 then z.1 else -z.1) := by
  fin_cases j <;> cases r₀ <;> cases r₁ <;>
    simp [pairedArmReindex,eq_comm,neg_eq_iff_eq_neg] <;> constructor <;> intro h <;> linarith

theorem SeparatedCircleSource.exists_original_oriented_collars
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
    ∃ (A : Fin 2 → Set P2) (B : ∀ j, OrientedPolygonCollar L d (A j)) (τ : C3 → X),
      PolyhedralPLInCharts e τ (identityTube L d) ∧ MapsTo τ (identityTube L d) (interior R) ∧
      (∀ z ∈ identityTube L d, ∀ w ∈ identityTube L d,
        τ z = τ w ↔ z.1 = w.1 ∧ (z.2 : AddCircle (4 * L)) = (w.2 : AddCircle (4 * L))) ∧
      (∀ j, A j ⊆ if T.label j = 0 then interior S₀ else interior S₁) ∧
      (∀ j, (fun p : squareAnnulus L d => ((B j).chart p : P2)) '' {p | depth L p = 0} =
        if T.label j = 0 then C₀ else C₁) ∧
      (∀ j z, z ∈ identityTube L d →
        (τ z ∈ (if T.label j = 0 then f₀ '' S₀ else f₁ '' S₁) ↔
          z.1.2 = if j = 0 then z.1.1 else -z.1.1)) ∧
      ∀ (j : Fin 2) (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d)
        (p : squareAnnulus L d), (p : P2) = annulusMap L (by linarith [T.depth_pos,T.width_small])
          ((s : AddCircle (4 * L)),u) →
        (if T.label j = 0 then f₀ else f₁) ((B j).chart p) = τ (sourceTubeDiagonal j u,s) := by
  classical
  choose A c hc hsub hvalue hmiddle using D.exists_original_source_chart T hi hmi
  obtain ⟨B,τ,hτ,himage,hfib,⟨r₀,r₁,hr⟩,hcenter,hperiod⟩ :=
    exists_original_pair_oriented_polygon_collars (ContinuousLinearEquiv.refl ℝ P2) e
      T.depth_pos T.width_small A c hc (fun j => if T.label j = 0 then f₀ else f₁)
      T.tube T.tube_PL T.tube_fibers (fun j s hs u =>
        (hvalue j _).trans (T.period_value j s hs u))
  refine ⟨A,B,τ,hτ,fun z hz => T.tube_interior (himage.subset ⟨z,hz,rfl⟩),hfib,hsub,?_,?_,?_⟩
  · intro j
    rw [← hmiddle j]
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨(c j).symm ((B j).chart p),(hcenter j p).mpr hp,
        congrArg Subtype.val ((c j).apply_symm_apply _)⟩
    · rintro ⟨p,hp,rfl⟩
      let q := (B j).chart.symm (c j p)
      have hq : (B j).chart q = c j p := (B j).chart.apply_symm_apply _
      refine ⟨q,(hcenter j q).mp ?_,congrArg Subtype.val hq⟩
      rwa [hq,(c j).symm_apply_apply]
  · intro j z hz
    rw [hr]
    change T.tube (pairedTubeReindex r₀ r₁ z) ∈ _ ↔ _
    rw [D.identity_whole_sheet_iff T hi hmi hwhole₀ hwhole₁ j _
      ((pairedTubeReindex_mem r₀ r₁ L d z).mpr hz)]
    exact pairedArmReindex_sheet_iff r₀ r₁ j z.1
  · intro j s hs u p hp
    have hp' : p = ⟨annulusMap L (by linarith [T.depth_pos,T.width_small])
        ((s : AddCircle (4 * L)),u),annulus_period_point_mem T.depth_pos T.width_small _ u⟩ :=
      Subtype.ext hp
    rw [hp']
    exact hperiod j s hs u

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
