import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapCoordinates
import PoincareConjecture.Proofs.M25.Mathlib.IntervalReparametrization
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D

theorem capCertificate_exists_lowerCut_diffeomorph
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : ClosedModelCapData g) {r t : ℝ}
    (hr : -C.epsilon⁻¹ < r) (hrt : r < t)
    (ht : t < C.epsilon⁻¹) :
    let U : TopologicalSpace.Opens M :=
      ⟨C.carrier, C.carrier_open⟩
    let V : TopologicalSpace.Opens M :=
      ⟨interior (C.carrier \ C.region t C.epsilon⁻¹),
        isOpen_interior⟩
    ∃ (tau : OpenPartialHomeomorph ℝ ℝ)
      (F : Diffeomorph (𝓡 3) (𝓡 3) U V ∞),
      tau.source = Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ ∧
      tau.target = Ioo (-C.epsilon⁻¹) t ∧
      ContDiffOn ℝ ∞ (tau : ℝ → ℝ) tau.source ∧
      ContDiffOn ℝ ∞ tau.symm tau.target ∧
      StrictMonoOn (tau : ℝ → ℝ) tau.source ∧
      EqOn (tau : ℝ → ℝ) id (Ioc (-C.epsilon⁻¹) r) ∧
      EqOn (tau.symm : ℝ → ℝ) id (Ioc (-C.epsilon⁻¹) r) ∧
      (∀ x : U, x.val ∈ C.closed_core ∪
          C.region (-C.epsilon⁻¹) r → (F x).val = x.val) ∧
      (∀ y : V, y.val ∈ C.closed_core ∪
          C.region (-C.epsilon⁻¹) r → (F.symm y).val = y.val) ∧
      (∀ (q : UnitTwoSphere) (s : ℝ) (x : U),
        s ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ →
        x.val = C.coordinate_map (q, s) →
        (F x).val = C.coordinate_map (q, tau s)) ∧
      (∀ (q : UnitTwoSphere) (s : ℝ) (y : V),
        s ∈ Ioo (-C.epsilon⁻¹) t →
        y.val = C.coordinate_map (q, s) →
        (F.symm y).val = C.coordinate_map (q, tau.symm s)) := by
  classical
  let U : TopologicalSpace.Opens M := ⟨C.carrier, C.carrier_open⟩
  let N := C
  let L := C.epsilon⁻¹
  let V : TopologicalSpace.Opens M :=
    ⟨interior (C.carrier \ N.region t L), isOpen_interior⟩
  let W (s : ℝ) := C.closed_core ∪ N.region (-L) s
  change -L < r at hr
  change t < L at ht
  obtain ⟨tau, hts, htt, htf, hti, htm, htid, htiid⟩ :=
    Real.exists_smooth_interval_reparametrization hr (hrt.trans ht) hrt
  have hWr : IsOpen (W r) :=
    (C.end_neck_lower_cut_topology ⟨hr, hrt.trans ht⟩).2.1
  have hV : (V : Set M) = W t :=
    (C.end_neck_lower_cut_topology ⟨hr.trans hrt, ht⟩).2.2.2.1
  have hcore : C.closed_core = C.carrier \ N.end_chart.target := C.closed_core_eq_complement_end
  have hWsub (s : ℝ) : W s ⊆ C.carrier := by
    rintro x (hx | hx)
    · exact (hcore ▸ hx).1
    · exact C.end_chart_target_subset hx.1
  have hVsub : (V : Set M) ⊆ C.carrier := hV ▸ hWsub t
  have hheight {x : M} (hx : x ∈ N.end_chart.target) :
      (N.coordinate_inverse x).2 ∈ Ioo (-L) L := by
    exact (N.coordinate_inverse_mem x hx).2
  have hWheight {s : ℝ} {x : M} (hx : x ∈ W s) (hxN : x ∈ N.end_chart.target) :
      (N.coordinate_inverse x).2 ∈ Ioo (-L) s := by
    rcases hx with hx | hx
    · exact False.elim ((hcore ▸ hx).2 hxN)
    · exact hx.2
  have hmap {z : UnitTwoSphere × ℝ} (hz : z.2 ∈ Ioo (-L) L) :
      N.coordinate_map z ∈ N.end_chart.target := by
    apply N.coordinate_map_mem
    exact ⟨mem_univ _, hz⟩
  have hinv {z : UnitTwoSphere × ℝ} (hz : z.2 ∈ Ioo (-L) L) :
      N.coordinate_inverse (N.coordinate_map z) = z :=
    N.coordinate_inverse_map z hz
  have hforward {s : ℝ} (hs : s ∈ Ioo (-L) L) : tau s ∈ Ioo (-L) t :=
    htt ▸ tau.map_source (hts.symm ▸ hs)
  have hbackward {s : ℝ} (hs : s ∈ Ioo (-L) t) : tau.symm s ∈ Ioo (-L) L :=
    hts ▸ tau.map_target (htt.symm ▸ hs)
  let f : M → M := fun x => if x ∈ N.end_chart.target then
    N.coordinate_map ((N.coordinate_inverse x).1, tau (N.coordinate_inverse x).2) else x
  let k : M → M := fun x => if x ∈ N.end_chart.target then
    N.coordinate_map ((N.coordinate_inverse x).1, tau.symm (N.coordinate_inverse x).2) else x
  have hfN {x : M} (hx : x ∈ N.end_chart.target) :
      f x = N.coordinate_map ((N.coordinate_inverse x).1,
        tau (N.coordinate_inverse x).2) := if_pos hx
  have hkN {x : M} (hx : x ∈ N.end_chart.target) :
      k x = N.coordinate_map ((N.coordinate_inverse x).1,
        tau.symm (N.coordinate_inverse x).2) := if_pos hx
  have hfout {x : M} (hx : x ∉ N.end_chart.target) : f x = x := if_neg hx
  have hkout {x : M} (hx : x ∉ N.end_chart.target) : k x = x := if_neg hx
  have hfmem {x : M} (hx : x ∈ C.carrier) : f x ∈ (V : Set M) := by
    rw [hV]
    by_cases hxN : x ∈ N.end_chart.target
    · rw [hfN hxN]
      have hs := hforward (hheight hxN)
      have hsL : tau (N.coordinate_inverse x).2 ∈ Ioo (-L) L :=
        ⟨hs.1, hs.2.trans ht⟩
      refine Or.inr ⟨hmap hsL, ?_⟩
      rw [hinv hsL]
      exact hs
    · rw [hfout hxN]
      exact Or.inl (hcore.symm ▸ ⟨hx, hxN⟩)
  have hkmem {x : M} (hx : x ∈ (V : Set M)) : k x ∈ C.carrier := by
    by_cases hxN : x ∈ N.end_chart.target
    · rw [hkN hxN]
      exact C.end_chart_target_subset (hmap (hbackward (hWheight (hV ▸ hx) hxN)))
    · rw [hkout hxN]
      exact hVsub hx
  have hleft (x : M) : k (f x) = x := by
    by_cases hxN : x ∈ N.end_chart.target
    · have hs := hforward (hheight hxN)
      have hsL : tau (N.coordinate_inverse x).2 ∈ Ioo (-L) L :=
        ⟨hs.1, hs.2.trans ht⟩
      rw [hfN hxN, hkN (hmap hsL), hinv hsL]
      dsimp only
      rw [tau.left_inv (hts.symm ▸ hheight hxN)]
      exact N.coordinate_map_inverse hxN
    · rw [hfout hxN, hkout hxN]
  have hright {x : M} (hx : x ∈ (V : Set M)) : f (k x) = x := by
    by_cases hxN : x ∈ N.end_chart.target
    · have hs := hWheight (hV ▸ hx) hxN
      have hsL := hbackward hs
      rw [hkN hxN, hfN (hmap hsL), hinv hsL]
      dsimp only
      rw [tau.right_inv (htt.symm ▸ hs)]
      exact N.coordinate_map_inverse hxN
    · rw [hkout hxN, hfout hxN]
  have hffix {x : M} (hx : x ∈ W r) : f x = x := by
    by_cases hxN : x ∈ N.end_chart.target
    · have hs := hWheight hx hxN
      rw [hfN hxN, htid ⟨hs.1, hs.2.le⟩]
      exact N.coordinate_map_inverse hxN
    · exact hfout hxN
  have hkfix {x : M} (hx : x ∈ W r) : k x = x := by
    by_cases hxN : x ∈ N.end_chart.target
    · have hs := hWheight hx hxN
      rw [hkN hxN, htiid ⟨hs.1, hs.2.le⟩]
      exact N.coordinate_map_inverse hxN
    · exact hkout hxN
  let F0 : U → V := fun x => ⟨f x.val, hfmem x.property⟩
  let G0 : V → U := fun x => ⟨k x.val, hkmem x.property⟩
  have hcover (D : TopologicalSpace.Opens M) (hD : (D : Set M) ⊆ C.carrier) :
      (Subtype.val : D → M) ⁻¹' W r ∪
        (Subtype.val : D → M) ⁻¹' N.end_chart.target = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hxN : x.val ∈ N.end_chart.target
    · exact Or.inr hxN
    · exact Or.inl (Or.inl (hcore.symm ▸ ⟨hD x.property, hxN⟩))
  have hfSmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : U => f x.val) := by
    have hi : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : U => N.coordinate_inverse x.val)
        ((Subtype.val : U → M) ⁻¹' N.end_chart.target) :=
      N.coordinate_inverse_smooth.comp contMDiff_subtype_val.contMDiffOn (fun _ hx => hx)
    have htau : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞
        (fun x : U => tau (N.coordinate_inverse x.val).2)
        ((Subtype.val : U → M) ⁻¹' N.end_chart.target) :=
      htf.contMDiffOn.comp (contMDiff_snd.comp_contMDiffOn hi)
        (fun _ hx => hts.symm ▸ hheight hx)
    have hpair := (contMDiff_fst.comp_contMDiffOn hi).prodMk htau
    have hneck : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x : U => f x.val)
        ((Subtype.val : U → M) ⁻¹' N.end_chart.target) := by
      apply (N.coordinate_map_smooth.comp hpair ?_).congr (fun _ hx => hfN hx)
      intro x hx
      have hs := hforward (hheight hx)
      change ((N.coordinate_inverse x.val).1, tau (N.coordinate_inverse x.val).2) ∈
        univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
      exact ⟨mem_univ _, hs.1, hs.2.trans ht⟩
    exact contMDiff_of_contMDiffOn_union_of_isOpen
      (contMDiff_subtype_val.contMDiffOn.congr (fun _ hx => hffix hx)) hneck
      (hcover U Subset.rfl) (hWr.preimage continuous_subtype_val)
      (N.end_chart.open_target.preimage continuous_subtype_val)
  have hkSmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : V => k x.val) := by
    have hi : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun x : V => N.coordinate_inverse x.val)
        ((Subtype.val : V → M) ⁻¹' N.end_chart.target) :=
      N.coordinate_inverse_smooth.comp contMDiff_subtype_val.contMDiffOn (fun _ hx => hx)
    have htau : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞
        (fun x : V => tau.symm (N.coordinate_inverse x.val).2)
        ((Subtype.val : V → M) ⁻¹' N.end_chart.target) :=
      hti.contMDiffOn.comp (contMDiff_snd.comp_contMDiffOn hi)
        (fun x hx => htt.symm ▸ hWheight (hV ▸ x.property) hx)
    have hpair := (contMDiff_fst.comp_contMDiffOn hi).prodMk htau
    have hneck : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x : V => k x.val)
        ((Subtype.val : V → M) ⁻¹' N.end_chart.target) := by
      apply (N.coordinate_map_smooth.comp hpair ?_).congr (fun _ hx => hkN hx)
      intro x hx
      change ((N.coordinate_inverse x.val).1, tau.symm (N.coordinate_inverse x.val).2) ∈
        univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
      exact ⟨mem_univ _, hbackward (hWheight (hV ▸ x.property) hx)⟩
    exact contMDiff_of_contMDiffOn_union_of_isOpen
      (contMDiff_subtype_val.contMDiffOn.congr (fun _ hx => hkfix hx)) hneck
      (hcover V hVsub) (hWr.preimage continuous_subtype_val)
      (N.end_chart.open_target.preimage continuous_subtype_val)
  let F : Diffeomorph (𝓡 3) (𝓡 3) U V ∞ :=
    { toFun := F0
      invFun := G0
      left_inv := fun x => Subtype.ext (hleft x.val)
      right_inv := fun x => Subtype.ext (hright x.property)
      contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff V F0).mp hfSmooth
      contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U G0).mp hkSmooth }
  refine ⟨tau, F, hts, htt, htf, hti, htm, htid, htiid,
    fun _ hx => hffix hx, fun _ hx => hkfix hx, ?_, ?_⟩
  · intro q s x hs hx
    change f x.val = _
    rw [hx, hfN (hmap hs), hinv hs]
  · intro q s y hs hy
    change k y.val = _
    have hsL : s ∈ Ioo (-L) L := ⟨hs.1, hs.2.trans ht⟩
    rw [hy, hkN (hmap hsL), hinv hsL]

end PoincareConjecture.M25.Topology3D
