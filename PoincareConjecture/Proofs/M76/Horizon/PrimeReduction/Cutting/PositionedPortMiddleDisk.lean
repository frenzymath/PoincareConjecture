import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.OriginalFinitePLBallImage
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBallTopology
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortRegionProduct










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem original_two_port_level_disk
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {d bd : Set P2} {region band S : Set X} (caps : Bool → Set X)
    (hd : IsFinitePLBallPair P2 d bd)
    (C : (d × unitInterval) ≃ₜ region) (p : P3 → X)
    (hp : PolyhedralPLInCharts e p (d ×ˢ I))
    (hpval : ∀ z : (d ×ˢ I : Set P3), p z = (C ((Homeomorph.Set.prod _ _) z) : X))
    (hcaps : ∀ b z, (C z : X) ∈ caps b ↔ z.2 = if b then 1 else 0)
    (hfront : frontier region = band ∪ (caps true ∪ caps false))
    (hcontact : region ∩ S = band) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    let j : P2 → X := fun z => p (z,t)
    PolyhedralPLInCharts e j d ∧ InjOn j d ∧ MapsTo j d region ∧
      (∀ z ∈ d, j z ∈ S ↔ z ∈ bd) ∧ j '' bd ⊆ band ∧
      j '' (d \ bd) ⊆ interior region ∧
      ∀ b, Disjoint (j '' d) (caps b) := by
  let j : P2 → X := fun z => p (z,t)
  have ht : t ∈ I := ⟨ht0.le,ht1.le⟩
  have hpi : InjOn p (d ×ˢ I) := by
    intro z hz w hw hzw
    have hh : C ((Homeomorph.Set.prod _ _) ⟨z,hz⟩) =
        C ((Homeomorph.Set.prod _ _) ⟨w,hw⟩) := Subtype.ext
      ((hpval ⟨z,hz⟩).symm.trans (hzw.trans (hpval ⟨w,hw⟩)))
    exact congrArg Subtype.val ((Homeomorph.Set.prod _ _).injective (C.injective hh))
  have hpimage : p '' (d ×ˢ I) = region := by
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      rw [hpval ⟨z,hz⟩]
      exact (C _).property
    · intro x hx
      let z : (d ×ˢ I : Set P3) := (Homeomorph.Set.prod _ _).symm (C.symm ⟨x,hx⟩)
      refine ⟨z,z.property,?_⟩
      rw [hpval]
      change (C ((Homeomorph.Set.prod d I)
        ((Homeomorph.Set.prod d I).symm (C.symm ⟨x,hx⟩))) : X) = x
      rw [Homeomorph.apply_symm_apply,C.apply_symm_apply]
  have hprod : IsFinitePLBallPair P3 (d ×ˢ I) ((bd ×ˢ I) ∪ (d ×ˢ {0,1})) :=
    hd.prod (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨ball⟩ := exists_chartwisePLBall_image hprod
    (ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod]) : P3 ≃L[ℝ] (Fin 3 → ℝ))
    hp subset_rfl hpi
  have hpfront : frontier region = p '' ((bd ×ˢ I) ∪ (d ×ˢ {0,1})) := by
    simpa only [hpimage] using ball.frontier_eq
  have hjfront (z : P2) (hz : z ∈ d) : j z ∈ frontier region ↔ z ∈ bd := by
    rw [hpfront]
    constructor
    · rintro ⟨w,hw,heq⟩
      have hwz : w = (z,t) := hpi (hprod.1 hw) ⟨hz,ht⟩ heq
      rw [hwz] at hw
      rcases hw with hw | hw
      · exact hw.1
      · have hte : t = 0 ∨ t = 1 := hw.2
        rcases hte with hte | hte <;> linarith
    · intro hzb
      exact ⟨(z,t),Or.inl ⟨hzb,ht⟩,rfl⟩
  have hjR : MapsTo j d region := fun z hz => hpimage.subset ⟨(z,t),⟨hz,ht⟩,rfl⟩
  have hmiss (b : Bool) : Disjoint (j '' d) (caps b) := by
    apply disjoint_left.mpr
    rintro _ ⟨z,hz,rfl⟩ hcap
    have hh : (C (⟨z,hz⟩,⟨t,ht⟩) : X) ∈ caps b := by
      have hval : p (z,t) = (C (⟨z,hz⟩,⟨t,ht⟩) : X) := hpval ⟨(z,t),hz,ht⟩
      change p (z,t) ∈ caps b at hcap
      rwa [hval] at hcap
    have hh' := congrArg Subtype.val ((hcaps b (⟨z,hz⟩,⟨t,ht⟩)).mp hh)
    cases b <;> norm_num at hh' <;> linarith
  have hjproper (z : P2) (hz : z ∈ d) : j z ∈ S ↔ z ∈ bd := by
    constructor
    · intro hs
      have hb := hcontact.subset ⟨hjR hz,hs⟩
      exact (hjfront z hz).mp (hfront.symm.subset (Or.inl hb))
    · intro hzb
      have hb : j z ∈ band := by
        rcases hfront.subset ((hjfront z hz).mpr hzb) with hb | hc
        · exact hb
        · rcases hc with hc | hc
          · exact False.elim (disjoint_left.mp (hmiss true) ⟨z,hz,rfl⟩ hc)
          · exact False.elim (disjoint_left.mp (hmiss false) ⟨z,hz,rfl⟩ hc)
      exact (hcontact.symm.subset hb).2
  have hdCopy := hd
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hdCopy
  have hjPL : PolyhedralPLInCharts e j d := by
    rw [←hKs]
    exact hp.comp_finitePiecewiseAffineOn K hK
      ⟨K,hK,rfl,K.affineOnFaces_affine
        ((ContinuousAffineMap.id ℝ P2).prod (ContinuousAffineMap.const ℝ P2 t))⟩
      (fun z hz => ⟨hKs.subset hz,ht⟩)
  refine ⟨hjPL,?_,hjR,hjproper,?_,?_,hmiss⟩
  · intro z hz w hw hzw
    exact congrArg Prod.fst (hpi ⟨hz,ht⟩ ⟨hw,ht⟩ hzw)
  · rintro _ ⟨z,hz,rfl⟩
    exact hcontact.subset ⟨hjR (hd.1 hz),(hjproper z (hd.1 hz)).mpr hz⟩
  · rintro _ ⟨z,⟨hz,hzb⟩,rfl⟩
    have hnot : j z ∉ frontier region := fun h => hzb ((hjfront z hz).mp h)
    by_contra hi
    exact hnot ⟨subset_closure (hjR hz),hi⟩

end PoincareConjecture.M76
