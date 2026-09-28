import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroPeriodLattice
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroPunctureConnected
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroPuncturedAtlas
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "T" => ((StableTorus.Circle × StableTorus.Circle) × StableTorus.Circle)
local notation "W" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "V3" => (Fin 3 → ℝ)




noncomputable def hamiltonZeroHandleProductEquiv : W ≃ₜ T :=
  (Homeomorph.uniqueProd (Fin 0 → ℝ) _).trans hamiltonZeroLatticeProductEquiv



def hamiltonZeroHandlePuncture : W :=
  (0, QuotientAddGroup.mk (fun _ : Fin 3 => (32 : ℝ)))



noncomputable def hamiltonZeroPunctureModelEquiv :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    ({hamiltonZeroHandlePuncture}ᶜ : Set W) ≃ₜ
      ({AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0}ᶜ : Set T) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  have hp : hamiltonZeroHandleProductEquiv hamiltonZeroHandlePuncture =
      AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0 :=
    hamiltonZeroLatticeProductEquiv_puncture
  apply hamiltonZeroHandleProductEquiv.subtype
  intro x
  simp only [mem_compl_iff, mem_singleton_iff]
  rw [← hp]
  exact (not_congr hamiltonZeroHandleProductEquiv.injective.eq_iff).symm





theorem exists_zero_lattice_punctured_PL_domain
    (h : OpenPartialHomeomorph CubeShell.Ambient V3) (hsource : h.source = univ) :
    let Y := ({hamiltonZeroHandlePuncture}ᶜ : Set W)
    ∃ (f : W → CubeShell.Ambient) (e : Y → OpenPartialHomeomorph Y V3),
      IsLocalHomeomorphOn f Y ∧ PLDomain e univ ∧
      IsConnected (univ : Set Y) ∧ HasOneSimplyConnectedEnd (univ : Set Y) ∧
      (∀ i, EqOn (e i) (fun x : Y => h (f x)) (e i).source) ∧
      ∃ (r : ℝ) (i : Y), 0 < r ∧ r ≤ 1 / 64 ∧
        ∀ x : V3, ‖x‖ ≤ r →
          ∃ z : Y, (z : W) = (0, QuotientAddGroup.mk x) ∧
            z ∈ (e i).source ∧ e i z = h (CubeShell.vector x) := by
  classical
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let Q := AddCircle.centeredCubeQuotient (4 * (16 : ℝ))
  let YT : Set T := {Q 0}ᶜ
  let Y : Set W := {hamiltonZeroHandlePuncture}ᶜ
  let a : W ≃ₜ T := hamiltonZeroHandleProductEquiv
  let b : Y ≃ₜ YT := hamiltonZeroPunctureModelEquiv
  obtain ⟨f, e, hf, he, heq, r, i, hr, hr64, hretained⟩ :=
    exists_zero_punctured_torus_PL_domain h hsource
  let e' : Y → OpenPartialHomeomorph Y V3 := fun j =>
    b.transOpenPartialHomeomorph (e (b j))
  have heq' (j : Y) : EqOn (e' j) (fun x : Y => h (f (a x))) (e' j).source := by
    intro x hx
    exact heq (b j) hx
  have hdomain : PLDomain e' univ := {
    cover := by
      intro x
      obtain ⟨j, hj⟩ := he.cover (b x)
      refine ⟨b.symm j, ?_⟩
      change b x ∈ (e (b (b.symm j))).source
      simpa only [b.apply_symm_apply] using hj
    compatible := by
      intro j k
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      apply (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ V3)
        ((e' j).symm.trans (e' k)).open_source).congr
      intro v hv
      change v = e' k ((e' j).symm v)
      have hkv : (e' j).symm v ∈ (e' k).source := hv.2
      have hjv : (e' j).symm v ∈ (e' j).source := (e' j).symm.map_source hv.1
      rw [heq' k hkv, ← heq' j hjv]
      exact ((e' j).right_inv hv.1).symm
    closed := isClosed_univ
    halfspace := by intro x hx; simp only [frontier_univ, mem_empty_iff_false] at hx
  }
  have hconn : IsConnected (univ : Set Y) := by
    have hconnT : IsConnected (univ : Set YT) := zero_punctured_torus_domain_isConnected
    simpa only [preimage_univ] using b.isConnected_preimage.mpr hconnT
  have hend : HasOneSimplyConnectedEnd (univ : Set Y) := by
    have h0 : (0 : CubeShell.Ambient) ∈ Q.source := by
      rw [AddCircle.centeredCubeQuotient_source]
      norm_num
    apply hasOneSimplyConnectedEnd_of_chart_puncture Q h0
      (by norm_num [CubeShell.Ambient, Module.finrank_prod])
      (fun x : (univ : Set Y) => (b (x : Y) : T))
      (Topology.IsEmbedding.subtypeVal.comp
        (b.isEmbedding.comp Topology.IsEmbedding.subtypeVal))
    ext t
    constructor
    · rintro ⟨x, rfl⟩
      exact (b (x : Y)).property
    · intro ht
      let tY : YT := ⟨t, ht⟩
      exact ⟨⟨b.symm tY, mem_univ _⟩,
        congrArg Subtype.val (b.apply_symm_apply tY)⟩
  refine ⟨f ∘ a, e', hf.comp a.isLocalHomeomorph.isLocalHomeomorphOn
    (fun x hx => (b ⟨x, hx⟩).property), hdomain, hconn, hend, heq',
    r, b.symm i, hr, hr64, ?_⟩
  intro x hx
  have hv : ‖CubeShell.vector x‖ ≤ r := by
    apply (CubeShell.norm_le_iff _ _).mpr
    intro j
    rw [CubeShell.coordinate_vector]
    have hnorm : |x j| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
    exact hnorm.trans hx
  obtain ⟨z, hz, hzi, hzformula⟩ := hretained (CubeShell.vector x) hv
  refine ⟨b.symm z, ?_, ?_, ?_⟩
  · apply a.injective
    have hb : a (b.symm z : W) = (z : T) :=
      congrArg Subtype.val (b.apply_symm_apply z)
    rw [hb, hz]
    exact (hamiltonZeroLatticeProductEquiv_mk x).symm
  · change b (b.symm z) ∈ (e (b (b.symm i))).source
    simpa only [b.apply_symm_apply] using hzi
  · change e (b (b.symm i)) (b (b.symm z)) = h (CubeShell.vector x)
    simpa only [b.apply_symm_apply] using hzformula

end PoincareConjecture.M76
