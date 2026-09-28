import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Polyhedra.Mathlib.LocallyInjectivePLLift
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition
import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarEndpointPL
import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetPhaseRetractionPL
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusReflection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
local notation "I" => Icc (0 : ℝ) 1

theorem Dehn.finitePiecewiseAffineOn_annulus_rim_period (b : Bool) :
    FinitePiecewiseAffineOn (fun s : ℝ =>
      (Dehn.annulusRimPoint b ((32 * s : ℝ) : Circle) : ℝ × ℝ)) I := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  let a : ℝ →ᴬ[ℝ] (ℝ × ℝ) :=
    ((32 : ℝ) • ContinuousAffineMap.id ℝ ℝ).prod
      (ContinuousAffineMap.const ℝ ℝ (if b then 1 else -1))
  have ha : FinitePiecewiseAffineOn a I := ⟨K, hK, hKI, K.affineOnFaces_affine a⟩
  have h := (finitePiecewiseAffineOn_wrappedStripMap
    (L := 8) (d := 1) (by norm_num) (by norm_num)).comp ha (by
      intro s hs
      change (32 * s, (if b then 1 else -1 : ℝ)) ∈ rectangle (4 * 8) 1
      refine ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
      cases b <;> norm_num)
  apply h.congr
  intro s hs
  exact (annulusMap_coe (L := 8) (t := if b then 1 else -1) (s := 32 * s)
    (by norm_num) (by cases b <;> norm_num)
    ⟨by linarith [hs.1], by linarith [hs.2]⟩).symm

private theorem exists_rim_period_parameter (z : Circle) :
    ∃ s ∈ I, ((32 * s : ℝ) : Circle) = z := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let t : ℝ := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
  have ht : t ∈ Ico 0 32 := by
    have ht := (AddCircle.equivIco (4 * (8 : ℝ)) 0 z).property
    change 0 ≤ t ∧ t < 0 + 4 * 8 at ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  refine ⟨t / 32, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  rw [show 32 * (t / 32) = t by ring]
  exact AddCircle.coe_equivIco

theorem finitePiecewiseAffineOn_hamiltonZero_lifted_annulus_rims
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j : (ℝ × ℝ) → X0} (hj : PolyhedralPLInCharts e j Ann)
    {theta : C0} {alpha : ℝ}
    (hphase : ∀ z : Ann, (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 = theta)
    (hlower : ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).2 =
        (alpha : C0))
    (hcover : IsCoveringMap (fun z : Circle =>
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).1.1))
    (H : Circle ≃ₜ Circle)
    (hlift : ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false (H z))))).1.1 =
        (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint true z)))).1.1) :
    ∀ b : Bool, FinitePiecewiseAffineOn (fun s : ℝ =>
      annulusMap 8 (by norm_num) (H ((32 * s : ℝ) : Circle), if b then 1 else -1)) I := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let rim : Circle → ℝ × ℝ := fun z => Dehn.annulusRimPoint false z
  let Y : (ℝ × ℝ) → X0 := fun z => hamiltonZeroAmbientMap phi (j z)
  let g : Circle → C0 := fun z => (Q0 (Y (rim z))).1.1
  obtain ⟨P, hP, hPs⟩ := (Dehn.finitePiecewiseAffineOn_annulus_rim_period false).exists_finite_triangulation_image
  have hPrange : P.space = range rim := by
    rw [hPs]
    ext x
    constructor
    · rintro ⟨s, _, rfl⟩
      exact ⟨((32 * s : ℝ) : Circle), rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨s, hs, hsz⟩ := exists_rim_period_parameter z
      exact ⟨s, hs, by simp only [hsz]; rfl⟩
  have hPr : MapsTo rim univ P.space := fun z _ => hPrange.symm.subset ⟨z, rfl⟩
  have hPAnn : P.space ⊆ Ann := by
    rw [hPrange]
    rintro _ ⟨z, rfl⟩
    exact (Dehn.annulusRimPoint false z).property
  have hrimc : Continuous rim := continuous_subtype_val.comp (Dehn.continuous_annulusRimPoint false)
  have hrimi : Function.Injective rim := by
    intro z w heq
    exact Dehn.injective_annulusRimPoint false (Subtype.ext heq)
  let r : Circle ≃ₜ P.space :=
    (hrimc.isClosedEmbedding hrimi).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hPrange.symm)
  have hr (z : Circle) : (r z : ℝ × ℝ) = rim z := rfl
  have hri (x : P.space) : rim (r.symm x) = x := by
    rw [← hr, r.apply_symm_apply]
  have hYi : IsLocallyInjective (fun x : P.space => Y x) := by
    intro x
    obtain ⟨U, hU, hxU, hgU⟩ := hcover.isLocalHomeomorph.isLocallyInjective (r.symm x)
    refine ⟨r.symm ⁻¹' U, hU.preimage r.symm.continuous, hxU, ?_⟩
    intro y hy z hz heq
    apply r.symm.injective
    apply hgU hy hz
    change g (r.symm y) = g (r.symm z)
    dsimp only [g]
    rw [hri, hri]
    exact congrArg (fun y => (Q0 y).1.1) heq
  have hYP : PolyhedralPLInCharts d Y P.space :=
    hphi.polyhedralPL_hamiltonZeroAmbientMap_comp P hP (hj.restrict_finite P hP hPAnn)
  obtain ⟨K, hK, hKI, _⟩ := Dehn.finitePiecewiseAffineOn_annulus_rim_period true
  let upper : ℝ → ℝ × ℝ := fun s => Dehn.annulusRimPoint true ((32 * s : ℝ) : Circle)
  have hupper : FinitePiecewiseAffineOn upper K.space := by
    rw [hKI]
    exact Dehn.finitePiecewiseAffineOn_annulus_rim_period true
  have hupperAnn : MapsTo upper K.space Ann := fun s _ =>
    (Dehn.annulusRimPoint true ((32 * s : ℝ) : Circle)).property
  have hYU := hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK
    (hj.comp_finitePiecewiseAffineOn K hK hupper hupperAnn)
  let q : ℝ → ℝ × ℝ := fun s => rim (H ((32 * s : ℝ) : Circle))
  have hq : Continuous q := hrimc.comp (H.continuous.comp
    ((AddCircle.continuous_mk' (4 * (8 : ℝ))).comp (continuous_const.mul continuous_id)))
  have hqP : MapsTo q K.space P.space := fun s _ => hPr (mem_univ _)
  have hYq : PolyhedralPLInCharts d (Y ∘ q) K.space := by
    apply (hd.polyhedralPL_hamiltonZeroTargetPhaseRetraction alpha hYU).congr
    intro s hs
    apply (Q0).injective
    rw [Function.comp_apply, hamiltonZeroTargetPhaseRetraction_coordinates]
    apply Prod.ext
    · apply Prod.ext
      · exact (hlift ((32 * s : ℝ) : Circle)).symm
      · exact (hphase (Dehn.annulusRimPoint true _)).trans
          (hphase (Dehn.annulusRimPoint false _)).symm
    · exact (hlower (H ((32 * s : ℝ) : Circle))).symm
  have hqPL : FinitePiecewiseAffineOn q I := by
    rw [← hKI]
    exact hYP.finitePiecewiseAffineOn_lift_of_locallyInjective
      hphi.target_domain.compatible P hP hYi K hK hq.continuousOn hqP hYq
  intro b
  cases b
  · exact hqPL
  · obtain ⟨R, ⟨f, hf, hfv⟩, _, hR⟩ :=
      _root_.Dehn.exists_square_annulus_depth_reflection (L := 8) (d := 1)
        (by norm_num) (by norm_num)
    have hqAnn : MapsTo q I Ann := fun s _ =>
      (Dehn.annulusRimPoint false (H ((32 * s : ℝ) : Circle))).property
    apply (hf.comp hqPL hqAnn).congr
    intro s hs
    obtain ⟨t, ht, htz⟩ := exists_rim_period_parameter (H ((32 * s : ℝ) : Circle))
    have ht32 : 32 * t ∈ Icc 0 (4 * (8 : ℝ)) :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hval := hR (32 * t) ht32 ⟨-1, by norm_num⟩
    rw [htz] at hval
    have hfv' := hfv (Dehn.annulusRimPoint false (H ((32 * s : ℝ) : Circle)))
    exact hfv'.symm.trans (by simpa [Dehn.annulusRimPoint] using hval)

end PoincareConjecture.M76
