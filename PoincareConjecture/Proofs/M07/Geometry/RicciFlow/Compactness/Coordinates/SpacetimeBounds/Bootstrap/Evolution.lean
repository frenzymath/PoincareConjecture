import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.PartialDerivatives










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.SpacetimeBounds.Bootstrap

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem deriv_spatialJet_eq_operator {n : ℕ} {Q : Jet E V n → V}
    {Ω : Set (Jet E V n)} (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    {f : ℝ × E → V} {J : Set ℝ} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : IsOpen J) (hU : IsOpen U)
    (hrange : ∀ z ∈ J ×ˢ U, spatialJet n f z ∈ Ω)
    (hevol : ∀ z ∈ J ×ˢ U, deriv (fun t => f (t, z.2)) z.1 = Q (spatialJet n f z))
    (j : ℕ) {z : ℝ × E} (hz : z ∈ J ×ˢ U) :
    deriv (fun t => iteratedFDeriv ℝ j (fun x => f (t, x)) z.2) z.1 =
      operator n Q j (spatialJet (n + j) f z) := by
  have hk (x : E) (hx : x ∈ U) :
      HasDerivAt (fun t => f (t, x)) (Q (spatialJet n f (z.1, x))) z.1 := by
    have hfull : ContDiffAt ℝ ∞ f (z.1, x) :=
      hf.contDiffAt ((hJ.prod hU).mem_nhds ⟨hz.1, hx⟩)
    have hd : DifferentiableAt ℝ (fun t => f (t, x)) z.1 :=
      (hfull.comp z.1
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    simpa only [hevol (z.1, x) ⟨hz.1, hx⟩] using hd.hasDerivAt
  exact (SpacetimeBounds.hasDerivAt_spatialJet hf hJ hU hz.1 hk j hz.2).deriv.trans
    (operator_spatialJet hΩ hQ hf hJ hU hrange hz.1 hz.2 j).symm




theorem eventuallyBounded_joint_spatial_jets {α : Type*} (l : Filter α)
    {n : ℕ} {Q : Jet E V n → V} {Ω : Set (Jet E V n)}
    (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (f : α → ℝ × E → V) (J : α → Set ℝ) (U : α → Set E) (S : α → Set (ℝ × E))
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (J a ×ˢ U a))
    (hJ : ∀ a, IsOpen (J a)) (hU : ∀ a, IsOpen (U a))
    (hS : ∀ a, S a ⊆ J a ×ˢ U a)
    (hrange : ∀ a z, z ∈ J a ×ˢ U a → spatialJet n (f a) z ∈ Ω)
    (hevol : ∀ a z, z ∈ J a ×ˢ U a →
      deriv (fun t => f a (t, z.2)) z.1 = Q (spatialJet n (f a) z))
    (hspatial : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ a in l, ∀ z ∈ S a,
      ‖iteratedFDeriv ℝ j (fun x => f a (z.1, x)) z.2‖ ≤ B)
    (hcompact : ∀ j, ∃ K : Set (Jet E V (n + j)), IsCompact K ∧
      K ⊆ (baseProjection n j) ⁻¹' Ω ∧
      ∀ᶠ a in l, MapsTo (spatialJet (n + j) (f a)) (S a) K) :
    ∀ m j, EventuallyBoundedJet l S
      (fun a z => iteratedFDeriv ℝ j (fun x => f a (z.1, x)) z.2) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro j
    cases m with
    | zero =>
      simpa only [EventuallyBoundedJet, norm_iteratedFDeriv_zero] using hspatial j
    | succ m =>
      have hsmooth (a : α) := SpacetimeBounds.contDiffOn_spatialJet (hf a) (hJ a) (hU a) j
      apply EventuallyBoundedJet.succ_of_partials hsmooth hJ hU hS
      · obtain ⟨K, hK, hKΩ, hKrange⟩ := hcompact j
        have hcomp : EventuallyBoundedJet l S
            (fun a => operator n Q j ∘ spatialJet (n + j) (f a)) m := by
          apply EventuallyBoundedJet.comp
            (hΩ.preimage (baseProjection n j).continuous) (contDiffOn_operator hΩ hQ j)
            hK hKΩ
            (fun a z hz => (contDiffOn_spatialJet (hf a) (hJ a) (hU a) (n + j)).contDiffAt
              (((hJ a).prod (hU a)).mem_nhds (hS a hz))) hKrange
          intro i hi
          apply EventuallyBoundedJet.pi
            (fun a z hz => (contDiffOn_spatialJet (hf a) (hJ a) (hU a) (n + j)).contDiffAt
              (((hJ a).prod (hU a)).mem_nhds (hS a hz)))
          intro k
          exact ih i (by omega) k
        obtain ⟨B, hB, hb⟩ := hcomp
        refine ⟨B, hB, ?_⟩
        filter_upwards [hb] with a ha z hz
        have heq : (fun w : ℝ × E => deriv (fun t =>
            iteratedFDeriv ℝ j (fun x => f a (t, x)) w.2) w.1) =ᶠ[𝓝 z]
            operator n Q j ∘ spatialJet (n + j) (f a) := by
          filter_upwards [((hJ a).prod (hU a)).mem_nhds (hS a hz)] with w hw
          exact deriv_spatialJet_eq_operator hΩ hQ (hf a) (hJ a) (hU a)
            (hrange a) (hevol a) j hw
        rw [(heq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
        exact ha z hz
      · obtain ⟨B, hB, hb⟩ := ih m (by omega) (j + 1)
        refine ⟨B, hB, ?_⟩
        filter_upwards [hb] with a ha z hz
        have heq : (fun w : ℝ × E =>
            fderiv ℝ (fun x => iteratedFDeriv ℝ j (fun y => f a (w.1, y)) x) w.2) =
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) V) ∘
              (fun w : ℝ × E => iteratedFDeriv ℝ (j + 1) (fun x => f a (w.1, x)) w.2) := rfl
        rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
        exact ha z hz

theorem eventuallyBounded_spacetime_jets {α : Type*} (l : Filter α)
    {n : ℕ} {Q : Jet E V n → V} {Ω : Set (Jet E V n)}
    (hΩ : IsOpen Ω) (hQ : ContDiffOn ℝ ∞ Q Ω)
    (f : α → ℝ × E → V) (J : α → Set ℝ) (U : α → Set E) (S : α → Set (ℝ × E))
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (J a ×ˢ U a))
    (hJ : ∀ a, IsOpen (J a)) (hU : ∀ a, IsOpen (U a))
    (hS : ∀ a, S a ⊆ J a ×ˢ U a)
    (hrange : ∀ a z, z ∈ J a ×ˢ U a → spatialJet n (f a) z ∈ Ω)
    (hevol : ∀ a z, z ∈ J a ×ˢ U a →
      deriv (fun t => f a (t, z.2)) z.1 = Q (spatialJet n (f a) z))
    (hspatial : ∀ j, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ a in l, ∀ z ∈ S a,
      ‖iteratedFDeriv ℝ j (fun x => f a (z.1, x)) z.2‖ ≤ B)
    (hcompact : ∀ j, ∃ K : Set (Jet E V (n + j)), IsCompact K ∧
      K ⊆ (baseProjection n j) ⁻¹' Ω ∧
      ∀ᶠ a in l, MapsTo (spatialJet (n + j) (f a)) (S a) K) :
    ∀ m, EventuallyBoundedJet l S f m := by
  intro m
  obtain ⟨B, hB, hb⟩ := eventuallyBounded_joint_spatial_jets l hΩ hQ f J U S
    hf hJ hU hS hrange hevol hspatial hcompact m 0
  refine ⟨B, hB, ?_⟩
  filter_upwards [hb] with a ha z hz
  have heq : (fun w : ℝ × E => iteratedFDeriv ℝ 0 (fun x => f a (w.1, x)) w.2) =
      (continuousMultilinearCurryFin0 ℝ E V).symm ∘ f a := rfl
  have hbz := ha z hz
  rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left] at hbz
  exact hbz

end PoincareConjecture.SpacetimeBounds.Bootstrap
