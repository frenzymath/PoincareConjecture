import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiniteInitialChart
import PoincareConjecture.Proofs.M25.AppA_21_Local.CapChainIntersection
import PoincareConjecture.Proofs.M25.Mathlib.CompatibleDiffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.exists_finite_chain_carrier_diffeomorph :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (C : CapCertificate g) (D : BalancedNeckChain g C.epsilon) {b : ℤ},
      D.shape = ChainShape.finite 0 b →
      C.epsilon ≤ epsilon0 →
      D.neck 0 = C.end_neck →
      (∀ i ∈ D.shape.active, (D.neck i).IsSeparating) →
      (∀ i ∈ D.shape.active, 0 < i → (D.neck i).center ∉ C.carrier) →
      let U : TopologicalSpace.Opens M :=
        ⟨C.carrier ∪ (⋃ i ∈ D.shape.active, (D.neck i).carrier),
          C.carrier_open.union
            (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
      let V : TopologicalSpace.Opens M := ⟨C.carrier, C.carrier_open⟩
      ∃ d : Diffeomorph (𝓡 3) (𝓡 3) U V ∞,
        (∀ x : U, x.val ∈ C.closed_core ∪
            C.end_neck.region (-C.epsilon⁻¹) 0 → (d x).val = x.val) ∧
        (∀ y : V, y.val ∈ C.closed_core ∪
            C.end_neck.region (-C.epsilon⁻¹) 0 → (d.symm y).val = y.val) := by
  obtain ⟨epsilon0, hpos, hcap, hchart⟩ :=
    BalancedNeckChain.exists_finite_initial_carrier_chart.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g C D b hshape hepsilon hstart hsep hout
  classical
  let T : Set M := ⋃ i ∈ D.shape.active, (D.neck i).carrier
  let N := C.end_neck
  let L := C.epsilon⁻¹
  let W : Set M := C.closed_core ∪ N.region (-L) 0
  let U : TopologicalSpace.Opens M :=
    ⟨C.carrier ∪ T, C.carrier_open.union
      (isOpen_iUnion fun i => isOpen_iUnion fun _ => (D.neck i).carrier_open)⟩
  let V : TopologicalSpace.Opens M := ⟨C.carrier, C.carrier_open⟩
  change ∃ d : Diffeomorph (𝓡 3) (𝓡 3) U V ∞,
    (∀ x : U, x.val ∈ W → (d x).val = x.val) ∧
    (∀ y : V, y.val ∈ W → (d.symm y).val = y.val)
  have hb : (0 : ℤ) ≤ b := by
    obtain ⟨i, hi⟩ := D.active_nonempty
    rw [hshape] at hi
    exact hi.1.trans hi.2
  have hzero : (0 : ℤ) ∈ D.shape.active := by
    rw [hshape]
    exact ⟨le_rfl, hb⟩
  have hfirst : ∀ i ∈ D.shape.active, (0 : ℤ) ≤ i := by
    intro i hi
    rw [hshape] at hi
    exact hi.1
  have hinter : C.carrier ∩ T = N.carrier :=
    C.inter_chain_union_eq_end_neck D hzero hfirst hstart hout
  have hNT : N.carrier ⊆ T := by
    intro x hx
    exact (show x ∈ C.carrier ∩ T from hinter.symm ▸ hx).2
  have hcore : C.closed_core = C.carrier \ N.carrier := C.closed_core_eq_complement_end
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have hWopen : IsOpen W :=
    (C.end_neck_lower_cut_topology ⟨neg_lt_zero.mpr hL, hL⟩).2.1
  have hWC : W ⊆ C.carrier := by
    rintro x (hx | hx)
    · exact (hcore ▸ hx).1
    · exact C.end_neck_subset hx.1
  have hWN : W ∩ N.carrier = N.region (-L) 0 := by
    ext x
    constructor
    · rintro ⟨hx | hx, hxN⟩
      · exact ((hcore ▸ hx).2 hxN).elim
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hx.1⟩
  have hWT : W ∩ T = N.region (-L) 0 := by
    ext x
    constructor
    · rintro ⟨hxW, hxT⟩
      have hxN : x ∈ N.carrier := hinter ▸ ⟨hWC hxW, hxT⟩
      exact hWN ▸ ⟨hxW, hxN⟩
    · intro hx
      exact ⟨Or.inr hx, hNT hx.1⟩
  have hcoverV : W ∪ N.carrier = C.carrier := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact hWC hx
      · exact C.end_neck_subset hx
    · intro x hx
      by_cases hxN : x ∈ N.carrier
      · exact Or.inr hxN
      · exact Or.inl (Or.inl (hcore.symm ▸ ⟨hx, hxN⟩))
  have hcoverU : W ∪ T = C.carrier ∪ T := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact Or.inl (hWC hx)
      · exact Or.inr hx
    · rintro x (hx | hx)
      · rcases (show x ∈ W ∪ N.carrier from hcoverV.symm ▸ hx) with hxW | hxN
        · exact Or.inl hxW
        · exact Or.inr (hNT hxN)
      · exact Or.inr hx
  obtain ⟨Q, hQs, hQt, hQ, hQi, hQfix, _⟩ :=
    hchart D hshape hepsilon hsep
  change Q.source = T at hQs
  have hQtN : Q.target = N.carrier := by simpa only [hstart] using hQt
  have hQnegative : EqOn (Q : M → M) id (N.region (-L) 0) := by
    simpa only [hstart] using hQfix
  have hNc : N.center ∈ N.carrier :=
    N.central_sphere_subset N.center_on_central_sphere
  let hU : Nonempty U := ⟨⟨N.center, Or.inl (C.end_neck_subset hNc)⟩⟩
  let hV : Nonempty V := ⟨⟨N.center, C.end_neck_subset hNc⟩⟩
  let I : OpenPartialHomeomorph M M := OpenPartialHomeomorph.ofSet W hWopen
  let J : OpenPartialHomeomorph M M :=
    OpenPartialHomeomorph.ofSet N.carrier N.carrier_open
  have hI : ContMDiffOn (𝓡 3) (𝓡 3) ∞ I I.source := contMDiff_id.contMDiffOn
  have hIi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ I.symm I.target := contMDiff_id.contMDiffOn
  have hJ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J J.source := contMDiff_id.contMDiffOn
  have hJi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J.symm J.target := contMDiff_id.contMDiffOn

  have restrictChart (A : TopologicalSpace.Opens M) (hA : Nonempty A)
      (e : OpenPartialHomeomorph M M) (hsub : e.source ⊆ (A : Set M))
      (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
      (hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
      let er := e.subtypeRestr hA
      er.source = (Subtype.val : A → M) ⁻¹' e.source ∧
      er.target = e.target ∧
      (er : A → M) = (fun x => e x.val) ∧
      (∀ z ∈ er.target, (er.symm z).val = e.symm z) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ er er.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ er.symm er.target := by
    let er := e.subtypeRestr hA
    have hrs : er.source = (Subtype.val : A → M) ⁻¹' e.source :=
      e.subtypeRestr_source hA
    have hrt : er.target = e.target := by
      change (e.subtypeRestr hA).target = e.target
      rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
        A.openPartialHomeomorphSubtypeCoe_target]
      exact inter_eq_left.mpr (fun z hz => hsub (e.map_target hz))
    have hri (z : M) (hz : z ∈ er.target) : (er.symm z).val = e.symm z :=
      e.subtypeRestr_symm_apply hA hz
    refine ⟨hrs, hrt, rfl, hri, ?_, ?_⟩
    · exact hf.comp contMDiff_subtype_val.contMDiffOn (fun x hx => hrs ▸ hx)
    · have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞
          (Subtype.val ∘ er.symm) er.target :=
        (hi.mono (fun _ hz => hrt ▸ hz)).congr hri
      intro z hz
      exact (ContMDiffWithinAt.subtypeVal_comp_iff A er.symm er.target z).mp (hcomp z hz)
  let e0 := I.subtypeRestr hU
  let e1 := Q.subtypeRestr hU
  let c0 := I.subtypeRestr hV
  let c1 := J.subtypeRestr hV
  obtain ⟨he0s, he0t, he0f, he0i, he0, hei0⟩ := restrictChart U hU I
    (fun x hx => Or.inl (hWC hx)) hI hIi
  obtain ⟨he1s, he1t, he1f, _, he1, hei1⟩ := restrictChart U hU Q
    (fun x hx => Or.inr (hQs ▸ hx)) hQ hQi
  obtain ⟨hc0s, hc0t, hc0f, hc0i, hc0, hci0⟩ := restrictChart V hV I hWC hI hIi
  obtain ⟨hc1s, hc1t, hc1f, _, hc1, hci1⟩ :=
    restrictChart V hV J C.end_neck_subset hJ hJi
  change e0.source = (Subtype.val : U → M) ⁻¹' W at he0s
  change e0.target = W at he0t
  change (e0 : U → M) = Subtype.val at he0f
  change ∀ z ∈ e0.target, (e0.symm z).val = z at he0i
  change e1.source = (Subtype.val : U → M) ⁻¹' Q.source at he1s
  change e1.target = Q.target at he1t
  rw [hQs] at he1s
  rw [hQtN] at he1t
  change c0.source = (Subtype.val : V → M) ⁻¹' W at hc0s
  change c0.target = W at hc0t
  change (c0 : V → M) = Subtype.val at hc0f
  change ∀ z ∈ c0.target, (c0.symm z).val = z at hc0i
  change c1.source = (Subtype.val : V → M) ⁻¹' N.carrier at hc1s
  change c1.target = N.carrier at hc1t
  change (c1 : V → M) = Subtype.val at hc1f
  have hecover : e0.source ∪ e1.source = univ := by
    rw [he0s, he1s, ← preimage_union, hcoverU]
    exact eq_univ_of_forall (fun x => x.property)
  have hccover : c0.source ∪ c1.source = univ := by
    rw [hc0s, hc1s, ← preimage_union, hcoverV]
    exact eq_univ_of_forall (fun x => x.property)
  have hesource : (e0.symm.trans e1).source = W ∩ T := by
    ext z
    change (z ∈ e0.target ∧ e0.symm z ∈ e1.source) ↔ z ∈ W ∩ T
    constructor
    · rintro ⟨hz, hx⟩
      refine ⟨he0t ▸ hz, ?_⟩
      rw [he1s] at hx
      change (e0.symm z).val ∈ T at hx
      rwa [he0i z hz] at hx
    · rintro ⟨hzW, hzT⟩
      have hz : z ∈ e0.target := he0t.symm ▸ hzW
      refine ⟨hz, ?_⟩
      rw [he1s]
      change (e0.symm z).val ∈ T
      rw [he0i z hz]
      exact hzT
  have hcsource : (c0.symm.trans c1).source = W ∩ N.carrier := by
    ext z
    change (z ∈ c0.target ∧ c0.symm z ∈ c1.source) ↔ z ∈ W ∩ N.carrier
    constructor
    · rintro ⟨hz, hx⟩
      refine ⟨hc0t ▸ hz, ?_⟩
      rw [hc1s] at hx
      change (c0.symm z).val ∈ N.carrier at hx
      rwa [hc0i z hz] at hx
    · rintro ⟨hzW, hzN⟩
      have hz : z ∈ c0.target := hc0t.symm ▸ hzW
      refine ⟨hz, ?_⟩
      rw [hc1s]
      change (c0.symm z).val ∈ N.carrier
      rw [hc0i z hz]
      exact hzN
  have htrans : OpenPartialHomeomorph.EqOnSource
      (e0.symm.trans e1) (c0.symm.trans c1) := by
    refine ⟨?_, ?_⟩
    · rw [hesource, hcsource, hWT, hWN]
    · intro z hz
      have hz0 : z ∈ e0.target := hz.1
      have hzc0 : z ∈ c0.target := hc0t.symm ▸ (he0t ▸ hz0)
      have hznegative : z ∈ N.region (-L) 0 := by
        rw [← hWT, ← hesource]
        exact hz
      change e1 (e0.symm z) = c1 (c0.symm z)
      rw [he1f, hc1f]
      change Q (e0.symm z).val = (c0.symm z).val
      rw [he0i z hz0, hc0i z hzc0]
      exact hQnegative hznegative
  obtain ⟨d, hd0, _, hdi0, _⟩ :=
    OpenPartialHomeomorph.m25_exists_diffeomorph_of_chart_transition e0 e1 c0 c1
      hecover hccover (he0t.trans hc0t.symm) (he1t.trans hc1t.symm)
      he0 he1 hei0 hei1 hc0 hc1 hci0 hci1 htrans
  refine ⟨d, ?_, ?_⟩
  · intro x hx
    have hx0 : x ∈ e0.source := he0s.symm ▸ hx
    have hz : e0 x ∈ c0.target :=
      (he0t.trans hc0t.symm) ▸ e0.map_source hx0
    have h := congrArg (Subtype.val : V → M) (hd0 hx0)
    change (d x).val = (c0.symm (e0 x)).val at h
    exact h.trans ((hc0i (e0 x) hz).trans (congrFun he0f x))
  · intro y hy
    have hy0 : y ∈ c0.source := hc0s.symm ▸ hy
    have hz : c0 y ∈ e0.target :=
      (hc0t.trans he0t.symm) ▸ c0.map_source hy0
    have h := congrArg (Subtype.val : U → M) (hdi0 hy0)
    change (d.symm y).val = (e0.symm (c0 y)).val at h
    exact h.trans ((he0i (c0 y) hz).trans (congrFun hc0f y))

end PoincareConjecture
