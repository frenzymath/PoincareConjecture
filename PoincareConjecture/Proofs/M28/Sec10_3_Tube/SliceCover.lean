import PoincareConjecture.Proofs.M28.Generalized.StrongNeckSlice
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PositiveComponent
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapAlternatives

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon epsilon₀ C : ℝ}

noncomputable def testedSliceNeckCapCover
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon₀)
    (hthreshold : epsilon₀ ≤ 1 / 200) (hC : 0 < C)
    (X : Set (F.slice t).carrier) (hX : IsConnected X)
    (hcanonical : ∀ x ∈ X, Nonempty (GeneralizedCanonicalControl (F := F) t x epsilon C))
    (hcomponent : ∀ N : SingularCComponent (F.metric t) (F.connection t) C,
      Disjoint X N.carrier)
    (hround : ∀ N : SingularRoundComponent (F.metric t) epsilon,
      Disjoint X N.carrier) : ConnectedNeckCapCover (F.metric t) := by
  have hhalf : epsilon < 1 / 2 := lt_of_le_of_lt (hsmall.trans hthreshold) (by norm_num)
  let necks : Set (EpsilonNeck (F.metric t)) :=
    {N | ∃ S : GeneralizedStrongNeck F t epsilon,
      N = strongNeck_top S hhalf ∧ S.center ∈ X}
  let caps : Set (CapCertificate (F.metric t)) :=
    {N | N.epsilon = epsilon ∧ N.cap_constant ≤ C ∧ N.connection = F.connection t}
  refine {
    epsilon := epsilon
    epsilon_pos := hepsilon
    epsilon_threshold := epsilon₀
    epsilon_threshold_pos := hepsilon.trans_le hsmall
    epsilon_threshold_le_one_two_hundred := hthreshold
    epsilon_le_threshold := hsmall
    cap_constant := C
    cap_constant_pos := hC
    X := X
    connected_X := hX
    necks := necks
    caps := caps
    pointwise_cover := ?_
    neck_epsilon := ?_
    cap_epsilon := fun N hN => hN.1
    cap_constant_bound := fun N hN => hN.2.1 }
  · intro x hx
    obtain ⟨hcan⟩ := hcanonical x hx
    cases hcan with
    | neck S hcenter =>
        exact Or.inl ⟨strongNeck_top S hhalf, ⟨S, rfl, hcenter ▸ hx⟩, hcenter⟩
    | cap N heps hconst hconn hcore =>
        exact Or.inr ⟨N, ⟨heps, hconst, hconn⟩, hcore⟩
    | component N hxN =>
        exact False.elim (Set.disjoint_left.mp (hcomponent N) hx hxN)
    | round N hxN =>
        exact False.elim (Set.disjoint_left.mp (hround N) hx hxN)
  · rintro N ⟨S, rfl, _⟩
    rfl

theorem testedSliceNeckCapCover_neck_provenance
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon₀)
    (hthreshold : epsilon₀ ≤ 1 / 200) (hC : 0 < C)
    (X : Set (F.slice t).carrier) (hX : IsConnected X)
    (hcanonical : ∀ x ∈ X, Nonempty (GeneralizedCanonicalControl (F := F) t x epsilon C))
    (hcomponent : ∀ N : SingularCComponent (F.metric t) (F.connection t) C,
      Disjoint X N.carrier)
    (hround : ∀ N : SingularRoundComponent (F.metric t) epsilon, Disjoint X N.carrier)
    (N : EpsilonNeck (F.metric t))
    (hN : N ∈ (testedSliceNeckCapCover hepsilon hsmall hthreshold hC X hX
      hcanonical hcomponent hround).necks) :
    ∃ S : GeneralizedStrongNeck F t epsilon,
      N = strongNeck_top S (lt_of_le_of_lt (hsmall.trans hthreshold) (by norm_num)) ∧
        S.center ∈ X := hN

theorem exists_tested_path_neck_cap_cover
    (P : RicciFlowCurvatureTheory.{u})
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon₀)
    (hthreshold : epsilon₀ ≤ 1 / 200) (hC : 0 < C)
    {a b : ℝ} (hab : a ≤ b) (γ : ℝ → (F.slice t).carrier)
    (hγ : ContinuousOn γ (Icc a b))
    (hcanonical : ∀ s ∈ Icc a b,
      Nonempty (GeneralizedCanonicalControl (F := F) t (γ s) epsilon C))
    (hlarge : C * F.scalar ⟨t, γ a⟩ < 6 * F.scalar ⟨t, γ b⟩)
    (hround : ∀ N : SingularRoundComponent (F.metric t) epsilon,
      Disjoint (γ '' Icc a b) N.carrier) :
    ∃ H : ConnectedNeckCapCover (F.metric t), H.X = γ '' Icc a b ∧
      H.epsilon = epsilon ∧ H.cap_constant = C ∧
      ∀ N ∈ H.necks, ∃ S : GeneralizedStrongNeck F t epsilon,
        N.center = S.center ∧ N.carrier = S.carrier ∧ N.scale = S.scale := by
  have hX : IsConnected (γ '' Icc a b) :=
    (isConnected_Icc hab).image γ hγ
  have hcan : ∀ x ∈ γ '' Icc a b,
      Nonempty (GeneralizedCanonicalControl (F := F) t x epsilon C) := by
    rintro _ ⟨s, hs, rfl⟩
    exact hcanonical s hs
  have hcomponent (N : SingularCComponent (F.metric t) (F.connection t) C) :
      Disjoint (γ '' Icc a b) N.carrier := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨s, hs, rfl⟩ hsN
    exact F.not_singularCComponent_on_path P t C hab γ hγ hlarge hs N hsN
  let H := testedSliceNeckCapCover hepsilon hsmall hthreshold hC
    (γ '' Icc a b) hX hcan hcomponent hround
  refine ⟨H, rfl, rfl, rfl, ?_⟩
  intro N hN
  obtain ⟨S, rfl, _⟩ := testedSliceNeckCapCover_neck_provenance hepsilon hsmall
    hthreshold hC (γ '' Icc a b) hX hcan hcomponent hround N hN
  exact ⟨S, rfl, rfl, rfl⟩

end PoincareConjecture.M28
