import PoincareConjecture.Proofs.M76.Triangulation.HamiltonZeroPunctureEnd

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "T" => ((StableTorus.Circle × StableTorus.Circle) × StableTorus.Circle)

theorem zero_punctured_torus_isConnected :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let p := AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0
    IsConnected ({p}ᶜ : Set T) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let a : StableTorus.Circle := (32 : ℝ)
  let C : Set StableTorus.Circle := {a}ᶜ
  let Q := AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) 32
  have hsource : IsConnected Q.source := by
    change IsConnected (Ioo (32 : ℝ) (32 + 4 * 16))
    exact isConnected_Ioo (by norm_num)
  have hC : IsConnected C := by
    have h := hsource.image Q Q.continuousOn
    rw [Q.image_source_eq_target] at h
    exact h
  have hwhole : IsConnected (univ : Set StableTorus.Circle) := isConnected_univ
  let S0 : Set T := (C ×ˢ univ) ×ˢ univ
  let S1 : Set T := (univ ×ˢ C) ×ˢ univ
  let S2 : Set T := univ ×ˢ C
  have hS0 : IsConnected S0 := (hC.prod hwhole).prod hwhole
  have hS1 : IsConnected S1 := (hwhole.prod hC).prod hwhole
  have hS2 : IsConnected S2 := isConnected_univ.prod hC
  obtain ⟨b, hb⟩ := hC.nonempty
  have h01 : (S0 ∩ S1).Nonempty :=
    ⟨((b, b), b), ⟨⟨⟨hb, mem_univ _⟩, mem_univ _⟩,
      ⟨⟨mem_univ _, hb⟩, mem_univ _⟩⟩⟩
  have h012 : ((S0 ∪ S1) ∩ S2).Nonempty :=
    ⟨((b, b), b), ⟨Or.inl ⟨⟨hb, mem_univ _⟩, mem_univ _⟩,
      ⟨mem_univ _, hb⟩⟩⟩
  have hconn : IsConnected ((S0 ∪ S1) ∪ S2) :=
    (hS0.union h01 hS1).union h012 hS2
  have hunion : (S0 ∪ S1) ∪ S2 = ({((a, a), a)}ᶜ : Set T) := by
    ext z
    simp only [S0, S1, S2, C, mem_union, mem_prod, mem_compl_iff,
      mem_singleton_iff, mem_univ, and_true, true_and]
    change ((z.1.1 ≠ a ∨ z.1.2 ≠ a) ∨ z.2 ≠ a) ↔ z ≠ ((a, a), a)
    rcases z with ⟨⟨x, y⟩, z⟩
    constructor
    · rintro ((hx | hy) | hz) heq
      · exact hx (congrArg (fun w : T => w.1.1) heq)
      · exact hy (congrArg (fun w : T => w.1.2) heq)
      · exact hz (congrArg (fun w : T => w.2) heq)
    · intro h
      by_contra hn
      push Not at hn
      exact h (Prod.ext (Prod.ext hn.1.1 hn.1.2) hn.2)
  rw [hunion] at hconn
  have hp : AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0 = ((a, a), a) := by
    rw [AddCircle.centeredCubeQuotient_apply]
    norm_num [a]
  simpa only [hp] using hconn

theorem zero_punctured_torus_domain_isConnected :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let p := AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0
    let Y := ({p}ᶜ : Set T)
    IsConnected (univ : Set Y) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let p := AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0
  let Y := ({p}ᶜ : Set T)
  have : ConnectedSpace Y :=
    isConnected_iff_connectedSpace.mp zero_punctured_torus_isConnected
  exact isConnected_univ

end PoincareConjecture.M76
