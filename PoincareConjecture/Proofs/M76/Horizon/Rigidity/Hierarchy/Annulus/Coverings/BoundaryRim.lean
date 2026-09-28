import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.SecondPhaseGroups
import Mathlib.Topology.Covering.Basic










set_option autoImplicit false
open Set Topology

namespace Poincare.Topology

def sndFiberHomeomorph {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (theta : Z) : {z : Y × Z | z.2 = theta} ≃ₜ Y where
  toFun z := z.1.1
  invFun y := ⟨(y, theta), rfl⟩
  left_inv z := Subtype.ext (Prod.ext rfl z.property.symm)
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := (continuous_id.prodMk continuous_const).subtype_mk _

theorem isCoveringMap_fst_restrict_snd
    {A Y Z : Type*} [TopologicalSpace A] [TopologicalSpace Y] [TopologicalSpace Z]
    {g : A → Y × Z} (hg : IsCoveringMap g) (theta : Z) :
    IsCoveringMap (fun x : {x : A | (g x).2 = theta} => (g x).1) :=
  (hg.restrictPreimage {z : Y × Z | z.2 = theta}).homeomorph_comp (sndFiberHomeomorph theta)

end Poincare.Topology

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_boundary_rim_circle_covering
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    (phi : C(H0, H0)) {R : Set X0}
    (c0 : K → X0) (hc0 : Continuous c0) (hi0 : Function.Injective c0)
    (hzero : range c0 = frontier R)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, (Q0 (hamiltonZeroAmbientMap phi (c0 x))).1 = g x)
    (theta : C0) :
    IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let T : Set K := {x | (g x).2 = theta}
  let S := frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}
  have hT : IsCompact T := (isClosed_eq g.continuous.snd continuous_const).isCompact
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  have hphase (x : K) : hamiltonZeroSecondCircleMap phi (c0 x) = (g x).2 := by
    rw [hamiltonZeroSecondCircleMap_ambient, hproduct]
  let f : T → S := fun x => ⟨c0 x,
    ⟨hzero.subset ⟨x, rfl⟩, (hphase x).trans x.property⟩⟩
  have hf : Continuous f := (hc0.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hi0 (congrArg Subtype.val hxy)
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hzero.symm.subset y.property.1
    have hxT : x ∈ T := by
      change (g x).2 = theta
      rw [← hphase, hx]
      exact y.property.2
    exact ⟨⟨x, hxT⟩, Subtype.ext hx⟩
  let H : T ≃ₜ S := hf.isClosedEmbedding hfi |>.isEmbedding.toHomeomorphOfSurjective hfs
  have hcover := (Poincare.Topology.isCoveringMap_fst_restrict_snd hg theta).comp_homeomorph H.symm
  convert hcover using 1
  funext y
  obtain ⟨x, rfl⟩ := H.surjective y
  change hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta (H x) =
    (g (H.symm (H x))).1
  rw [H.symm_apply_apply, hamiltonZeroSecondPhaseCircleMap_ambient]
  exact congrArg Prod.fst (hproduct x)

theorem hamiltonZero_installed_boundary_rim_circle_covering
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K)
    (phi : C(H0, H0)) {R : Set X0} {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X0)
    (hi : IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, ∀ t ∈ Icc (-r) r,
      (Q0 (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x)
    (theta : C0) :
    IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta) := by
  have hz : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  have hic : IsEmbedding (fun x : K => c (x, 0)) :=
    hi.comp ((Homeomorph.Set.prod K (Icc (-r) r)).symm.isEmbedding.comp
      (isEmbedding_prodMkLeft (⟨0, hz⟩ : Icc (-r) r)))
  have hrange : range (fun x : K => c (x, 0)) = frontier R := by
    rw [← hzero]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x, 0), ⟨x.property, rfl⟩, rfl⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      exact ⟨⟨x, hx⟩, by rw [ht0]⟩
  exact hamiltonZero_boundary_rim_circle_covering hK phi (fun x => c (x, 0))
    hic.continuous hic.injective hrange g hg (fun x => hproduct x 0 hz) theta

end PoincareConjecture.M76
