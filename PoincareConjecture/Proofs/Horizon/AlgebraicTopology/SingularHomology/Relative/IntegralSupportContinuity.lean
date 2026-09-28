import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Relative.IntegralSupportLocalization

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_open_integralRelativeProjection_support [T2Space X]
    (K : Set X) (n : Nat) (c : (integralChains X).X n)
    (hc : (integralRelativeProjection Kᶜ).f n c = 0) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      (integralRelativeProjection Uᶜ).f n c = 0 := by
  classical
  let F := (integralChainCoordinates X n c).support
  let S : Set X := ⋃ s ∈ F, Set.range s
  have hS : IsCompact S :=
    F.isCompact_biUnion (fun s _ => isCompact_range s.continuous)
  have hr : c ∈ LinearMap.range ((integralSubspaceChains Kᶜ).f n).hom :=
    (integralProjection_eq_zero_iff (integralSubspaceChains Kᶜ) n c).mp hc
  have hs := (integral_subspace_range_iff Kᶜ n c).mp hr
  refine ⟨Sᶜ, hS.isClosed.isOpen_compl, ?_, ?_⟩
  · intro x hx hxS
    obtain ⟨s, hsf, hxs⟩ := Set.mem_iUnion₂.mp hxS
    exact hs s hsf hxs hx
  · rw [compl_compl]
    apply (integralProjection_eq_zero_iff (integralSubspaceChains S) n c).mpr
    apply (integral_subspace_range_iff S n c).mpr
    intro s hsf y hy
    exact Set.mem_iUnion₂.mpr ⟨s, hsf, hy⟩

theorem exists_open_integralRelativeHomology_lift [T2Space X]
    (K : Set X) (n : Nat) (a : integralRelativeHomology Kᶜ n) :
    ∃ U : Set X, IsOpen U ∧ ∃ hKU : K ⊆ U,
      ∃ b : integralRelativeHomology Uᶜ n,
        homologyMap (integralRelativeRestriction (Set.compl_subset_compl.mpr hKU)) n b = a := by
  let C := integralChains X
  let R := integralRelativeChains Kᶜ
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (R.homologyπ n)).mp inferInstance a
  obtain ⟨c, hc⟩ := integralProjection_surjective (integralSubspaceChains Kᶜ) n
    (R.iCycles n z)
  let m := (ComplexShape.down Nat).next n
  have hdc : (integralRelativeProjection Kᶜ).f m (C.d n m c) = 0 := by
    have he := congrArg (fun g => g c) ((integralRelativeProjection Kᶜ).comm n m)
    change R.d n m ((integralRelativeProjection Kᶜ).f n c) =
      (integralRelativeProjection Kᶜ).f m (C.d n m c) at he
    rw [hc] at he
    exact he.symm.trans (congrArg (fun g => g z) (R.iCycles_d n m))
  obtain ⟨U, hU, hKU, hdU⟩ :=
    exists_open_integralRelativeProjection_support K m (C.d n m c) hdc
  let Q := integralRelativeChains Uᶜ
  let f : Q ⟶ R := integralRelativeRestriction (Set.compl_subset_compl.mpr hKU)
  let q : Q.X n := (integralRelativeProjection Uᶜ).f n c
  have hq : (Q.sc n).g q = 0 := by
    have he := congrArg (fun g => g c) ((integralRelativeProjection Uᶜ).comm n m)
    change Q.d n m q = (integralRelativeProjection Uᶜ).f m (C.d n m c) at he
    exact he.trans hdU
  let w : Q.cycles n := (Q.sc n).cyclesMk q hq
  have hw : Q.iCycles n w = q := (Q.sc n).i_cyclesMk q hq
  have hwz : cyclesMap f n w = z := by
    apply (ModuleCat.mono_iff_injective (R.iCycles n)).mp inferInstance
    have hi := congrArg (fun g => g w) (cyclesMap_i f n)
    change R.iCycles n (cyclesMap f n w) = f.f n (Q.iCycles n w) at hi
    rw [hi, hw]
    have hp := congrArg (fun g => g.f n c)
      (integralRelativeRestriction_projection (Set.compl_subset_compl.mpr hKU))
    change f.f n q = (integralRelativeProjection Kᶜ).f n c at hp
    exact hp.trans hc
  refine ⟨U, hU, hKU, Q.homologyπ n w, ?_⟩
  have he := congrArg (fun g => g w) (homologyπ_naturality (φ := f) (i := n))
  change homologyMap f n (Q.homologyπ n w) = R.homologyπ n (cyclesMap f n w) at he
  rw [hwz, hz] at he
  exact he

theorem exists_open_integralRelativeHomology_lift_forall [T2Space X]
    (K : Set X) (n : Nat) (a : integralRelativeHomology Kᶜ n) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧
      ∀ (L : Set X) (hKL : K ⊆ L), L ⊆ U →
        ∃ b : integralRelativeHomology Lᶜ n,
          homologyMap (integralRelativeRestriction
            (Set.compl_subset_compl.mpr hKL)) n b = a := by
  obtain ⟨U, hU, hKU, b, hb⟩ := exists_open_integralRelativeHomology_lift K n a
  refine ⟨U, hU, hKU, ?_⟩
  intro L hKL hLU
  refine ⟨homologyMap (integralRelativeRestriction (Set.compl_subset_compl.mpr hLU)) n b, ?_⟩
  have hc : integralRelativeRestriction (Set.compl_subset_compl.mpr hLU) ≫
      integralRelativeRestriction (Set.compl_subset_compl.mpr hKL) =
        integralRelativeRestriction (Set.compl_subset_compl.mpr hKU) := by
    rw [integralRelativeRestriction_comp]
  have he := congrArg (fun g : integralRelativeChains Uᶜ ⟶ integralRelativeChains Kᶜ =>
    homologyMap g n b) hc
  rw [homologyMap_comp] at he
  exact he.trans hb

end Poincare.Topology
