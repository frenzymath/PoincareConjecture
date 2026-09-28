import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.MayerVietoris.IntegralMayerVietoris
import Mathlib.Topology.Separation.Regular

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Poincare.Topology

variable {X : Type u} [TopologicalSpace X]

@[reassoc (attr := simp)]
theorem integralRelativeRestriction_comp {A B D : Set X}
    (hAB : A ⊆ B) (hBD : B ⊆ D) :
    integralRelativeRestriction hAB ≫ integralRelativeRestriction hBD =
      integralRelativeRestriction (hAB.trans hBD) := by
  apply (cancel_epi (integralRelativeProjection A)).mp
  rw [← Category.assoc, integralRelativeRestriction_projection,
    integralRelativeRestriction_projection, integralRelativeRestriction_projection]

theorem exists_open_integralRelativeProjection_eq_zero [T2Space X]
    (n : Nat) (c : (integralChains X).X n) (x : X)
    (hc : (integralRelativeProjection ({x}ᶜ : Set X)).f n c = 0) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (integralRelativeProjection Uᶜ).f n c = 0 := by
  classical
  let F := (integralChainCoordinates X n c).support
  let S : Set X := ⋃ s ∈ F, Set.range s
  have hS : IsCompact S :=
    F.isCompact_biUnion (fun s _ => isCompact_range s.continuous)
  have hr : c ∈ LinearMap.range
      ((integralSubspaceChains ({x}ᶜ : Set X)).f n).hom :=
    (integralProjection_eq_zero_iff (integralSubspaceChains ({x}ᶜ : Set X)) n c).mp hc
  have hs := (integral_subspace_range_iff ({x}ᶜ : Set X) n c).mp hr
  refine ⟨Sᶜ, hS.isClosed.isOpen_compl, ?_, ?_⟩
  · intro hx
    obtain ⟨s, hsf, hx⟩ := Set.mem_iUnion₂.mp hx
    exact hs s hsf hx rfl
  · rw [compl_compl]
    apply (integralProjection_eq_zero_iff (integralSubspaceChains S) n c).mpr
    apply (integral_subspace_range_iff S n c).mpr
    intro s hsf y hy
    exact Set.mem_iUnion₂.mpr ⟨s, hsf, hy⟩

private theorem homologyClass_zero_iff_boundary
    (C : ChainComplex (ModuleCat.{u} Int) Nat) (n : Nat) (z : C.cycles n) :
    C.homologyπ n z = 0 ↔
      ∃ b : C.X (n + 1), C.d (n + 1) n b = C.iCycles n z := by
  let S := ShortComplex.mk (C.toCycles (n + 1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n + 1) n)
  have hS : S.Exact := S.exact_of_g_is_cokernel
    (C.homologyIsCokernel (n + 1) n (by simp))
  constructor
  · intro hz
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS z hz
    refine ⟨b, ?_⟩
    have he := congrArg (C.iCycles n) hb
    simpa only [S, ← ConcreteCategory.comp_apply, toCycles_i] using he
  · rintro ⟨b, hb⟩
    have he : C.toCycles (n + 1) n b = z := by
      apply (ModuleCat.mono_iff_injective (C.iCycles n)).mp inferInstance
      simpa only [← ConcreteCategory.comp_apply, toCycles_i] using hb
    rw [← he]
    exact congrArg (fun f => f b) (C.toCycles_comp_homologyπ (n + 1) n)

theorem exists_open_integralRelativeHomology_restriction_eq_zero [T2Space X]
    (K : Set X) (n : Nat) (a : integralRelativeHomology Kᶜ n)
    (x : X) (hx : x ∈ K)
    (ha : homologyMap (integralRelativeRestriction
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) n a = 0) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      homologyMap (integralRelativeRestriction
        (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K))) n a = 0 := by
  let C := integralChains X
  let R := integralRelativeChains Kᶜ
  let P := integralRelativeChains ({x}ᶜ : Set X)
  let f : R ⟶ P := integralRelativeRestriction
    (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (R.homologyπ n)).mp inferInstance a
  obtain ⟨c, hc⟩ := integralProjection_surjective (integralSubspaceChains Kᶜ) n
    (R.iCycles n z)
  have hlocal : P.homologyπ n (cyclesMap f n z) = 0 := by
    have he := congrArg (fun g => g z) (homologyπ_naturality (φ := f) (i := n))
    change homologyMap f n (R.homologyπ n z) = P.homologyπ n (cyclesMap f n z) at he
    rw [hz] at he
    exact he.symm.trans ha
  obtain ⟨b, hb⟩ := (homologyClass_zero_iff_boundary P n _).mp hlocal
  obtain ⟨d, hd⟩ := integralProjection_surjective
    (integralSubspaceChains ({x}ᶜ : Set X)) (n + 1) b
  have hp : (integralRelativeProjection ({x}ᶜ : Set X)).f n c =
      P.iCycles n (cyclesMap f n z) := by
    have he := congrArg (fun g => g.f n c)
      (integralRelativeRestriction_projection
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx)))
    change f.f n ((integralRelativeProjection Kᶜ).f n c) =
      (integralRelativeProjection ({x}ᶜ : Set X)).f n c at he
    rw [hc] at he
    exact he.symm.trans
      (congrArg (fun g => g z) (cyclesMap_i f n)).symm
  have hres : (integralRelativeProjection ({x}ᶜ : Set X)).f n
      (c - C.d (n + 1) n d) = 0 := by
    rw [map_sub, hp]
    have he := congrArg (fun g => g d)
      ((integralRelativeProjection ({x}ᶜ : Set X)).comm (n + 1) n)
    change P.d (n + 1) n ((integralRelativeProjection ({x}ᶜ : Set X)).f (n + 1) d) =
      (integralRelativeProjection ({x}ᶜ : Set X)).f n (C.d (n + 1) n d) at he
    rw [hd, hb] at he
    exact sub_eq_zero.mpr he
  obtain ⟨U, hU, hxU, hresU⟩ :=
    exists_open_integralRelativeProjection_eq_zero n (c - C.d (n + 1) n d) x hres
  refine ⟨U, hU, hxU, ?_⟩
  let Q := integralRelativeChains (K ∩ U)ᶜ
  let g : R ⟶ Q := integralRelativeRestriction
    (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K))
  have hresQ : (integralRelativeProjection (K ∩ U)ᶜ).f n
      (c - C.d (n + 1) n d) = 0 := by
    have he := congrArg (fun k => k.f n (c - C.d (n + 1) n d))
      (integralRelativeRestriction_projection
        (Set.compl_subset_compl.mpr (Set.inter_subset_right : K ∩ U ⊆ U)))
    change (integralRelativeRestriction
        (Set.compl_subset_compl.mpr (Set.inter_subset_right : K ∩ U ⊆ U))).f n
        ((integralRelativeProjection Uᶜ).f n (c - C.d (n + 1) n d)) =
      (integralRelativeProjection (K ∩ U)ᶜ).f n
        (c - C.d (n + 1) n d) at he
    rw [hresU, map_zero] at he
    exact he.symm
  have hboundary : Q.homologyπ n (cyclesMap g n z) = 0 := by
    apply (homologyClass_zero_iff_boundary Q n _).mpr
    refine ⟨(integralRelativeProjection (K ∩ U)ᶜ).f (n + 1) d, ?_⟩
    have hdQ := congrArg (fun k => k d)
      ((integralRelativeProjection (K ∩ U)ᶜ).comm (n + 1) n)
    change Q.d (n + 1) n ((integralRelativeProjection (K ∩ U)ᶜ).f (n + 1) d) =
      (integralRelativeProjection (K ∩ U)ᶜ).f n (C.d (n + 1) n d) at hdQ
    rw [hdQ]
    rw [map_sub, sub_eq_zero] at hresQ
    rw [← hresQ]
    have he := congrArg (fun k => k.f n c)
      (integralRelativeRestriction_projection
        (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K)))
    change g.f n ((integralRelativeProjection Kᶜ).f n c) =
      (integralRelativeProjection (K ∩ U)ᶜ).f n c at he
    rw [hc] at he
    exact he.symm.trans
      (congrArg (fun k => k z) (cyclesMap_i g n)).symm
  have he := congrArg (fun k => k z) (homologyπ_naturality (φ := g) (i := n))
  change homologyMap g n (R.homologyπ n z) = Q.homologyπ n (cyclesMap g n z) at he
  rw [hz] at he
  exact he.trans hboundary

theorem exists_compact_integralRelativeHomology_restriction_eq_zero
    [T2Space X] [RegularSpace X]
    (K : Set X) (hK : IsCompact K) (n : Nat) (a : integralRelativeHomology Kᶜ n)
    (x : X) (hx : x ∈ K)
    (ha : homologyMap (integralRelativeRestriction
      (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hx))) n a = 0)
    (W : Set X) (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ V L : Set X, IsOpen V ∧ x ∈ V ∧ IsCompact L ∧ K ∩ V ⊆ L ∧
      ∃ hL : L ⊆ K ∩ W,
        homologyMap (integralRelativeRestriction
          (Set.compl_subset_compl.mpr (hL.trans Set.inter_subset_left))) n a = 0 := by
  obtain ⟨U, hU, hxU, haU⟩ :=
    exists_open_integralRelativeHomology_restriction_eq_zero K n a x hx ha
  obtain ⟨F, hxF, hF, hFUW⟩ := exists_mem_nhds_isClosed_subset
    ((hU.inter hW).mem_nhds ⟨hxU, hxW⟩)
  let L := K ∩ F
  have hLKU : L ⊆ K ∩ U := fun _ hy => ⟨hy.1, (hFUW hy.2).1⟩
  have hLKW : L ⊆ K ∩ W := fun _ hy => ⟨hy.1, (hFUW hy.2).2⟩
  refine ⟨interior F, L, isOpen_interior, mem_interior_iff_mem_nhds.mpr hxF,
    hK.inter_right hF, (fun _ hy => ⟨hy.1, interior_subset hy.2⟩), hLKW, ?_⟩
  have hc : integralRelativeRestriction
      (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K)) ≫
        integralRelativeRestriction (Set.compl_subset_compl.mpr hLKU) =
      integralRelativeRestriction
        (Set.compl_subset_compl.mpr (hLKW.trans Set.inter_subset_left)) := by
    rw [integralRelativeRestriction_comp]
  rw [← hc, homologyMap_comp]
  change homologyMap (integralRelativeRestriction (Set.compl_subset_compl.mpr hLKU)) n
    (homologyMap (integralRelativeRestriction
      (Set.compl_subset_compl.mpr (Set.inter_subset_left : K ∩ U ⊆ K))) n a) = 0
  rw [haU, map_zero]

end Poincare.Topology
