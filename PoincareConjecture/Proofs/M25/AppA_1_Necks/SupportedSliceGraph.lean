import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import PoincareConjecture.Proofs.M25.Mathlib.PositivePolar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyExtension









set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



theorem EpsilonNeck.exists_supported_slice_graph_straightening
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) (h : UnitTwoSphere → ℝ)
    (hh : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hdom : ∀ q, h q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (d : ℝ) (hd : d ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ Ψ : Diffeomorph (𝓡 3) (𝓡 3) M M ∞,
      (∃ K : Set M, IsCompact K ∧ K ⊆ N.carrier ∧
        ∀ x, x ∉ K → Ψ x = x) ∧
      Ψ '' range (fun q : UnitTwoSphere => N.coordinate_map (q, h q)) =
        range (fun q : UnitTwoSphere => N.coordinate_map (q, d)) := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let : Fact (Module.finrank ℝ E = 2 + 1) := ⟨by simp [E]⟩
  let L : ℝ := N.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr N.epsilon_pos
  let A : Set E := {x | 1 < ‖x‖ ∧ ‖x‖ < 3}
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  have hrad (t : ℝ) (ht : t ∈ Ioo (-L) L) : 2 + t / L ∈ Ioo (1 : ℝ) 3 := by
    have h1 : (-1 : ℝ) < t / L := (lt_div_iff₀ hL).mpr (by linarith [ht.1])
    have h2 : t / L < 1 := (div_lt_iff₀ hL).mpr (by linarith [ht.2])
    constructor <;> linarith
  let rh : UnitTwoSphere → ℝ := fun q => 2 + h q / L
  let rd : ℝ := 2 + d / L
  have hrh (q : UnitTwoSphere) : rh q ∈ Ioo (1 : ℝ) 3 := hrad (h q) (hdom q)
  have hrd : rd ∈ Ioo (1 : ℝ) 3 := hrad d hd
  have hrhs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ rh := by
    simpa only [rh, div_eq_mul_inv, Pi.add_def, Pi.mul_def] using
      ((contMDiff_const (c := (2 : ℝ))).add (hh.mul (contMDiff_const (c := L⁻¹))))
  obtain ⟨Q, hQs, hQt, _, hQheight, _, hQ, hQi⟩ :=
    exists_smooth_unitSpherePolar (E := E) (n := 2) (N.coordinate_inverse N.center).1
  have hQleft (q : UnitTwoSphere) (r : ℝ) (hr : 0 < r) :
      Q.symm (Q (q, r)) = (q, r) :=
    Q.left_inv (hQs.symm ▸ ⟨mem_univ _, hr⟩)
  have hQnorm (q : UnitTwoSphere) (r : ℝ) (hr : 0 < r) : ‖Q (q, r)‖ = r := by
    rw [← hQheight, hQleft q r hr]
  have hQA (q : UnitTwoSphere) {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 3) : Q (q, r) ∈ A := by
    change 1 < ‖Q (q, r)‖ ∧ ‖Q (q, r)‖ < 3
    rwa [hQnorm q r (by linarith [hr.1])]
  have hAQt : A ⊆ Q.target := by
    intro x hx
    rw [hQt]
    exact norm_pos_iff.mp (lt_trans (by norm_num) hx.1)
  have hJcoord (x : E) (hx : x ∈ A) :
      ((Q.symm x).1, L * ((Q.symm x).2 - 2)) ∈ N.cylinderDomain := by
    refine ⟨mem_univ _, ?_, ?_⟩ <;> rw [hQheight]
    · change -L < L * (‖x‖ - 2)
      nlinarith [hx.1]
    · change L * (‖x‖ - 2) < L
      nlinarith [hx.2]
  let j : E → M := fun x => N.coordinate_map
    ((Q.symm x).1, L * ((Q.symm x).2 - 2))
  let ji : M → E := fun x => Q
    ((N.coordinate_inverse x).1, 2 + (N.coordinate_inverse x).2 / L)
  have hj : MapsTo j A N.carrier := fun x hx => N.coordinate_map_mem (hJcoord x hx)
  have hji : MapsTo ji N.carrier A := fun x hx =>
    hQA _ (hrad _ (N.coordinate_inverse_mem x hx).2)
  have hjleft (x : E) (hx : x ∈ A) : ji (j x) = x := by
    dsimp only [ji, j]
    rw [N.coordinate_inverse_map _ (hJcoord x hx).2]
    have he : 2 + L * ((Q.symm x).2 - 2) / L = (Q.symm x).2 := by
      field_simp [hL.ne']
      ring
    rw [he]
    exact Q.right_inv (hAQt hx)
  have hjright (x : M) (hx : x ∈ N.carrier) : j (ji x) = x := by
    have hr := hrad _ (N.coordinate_inverse_mem x hx).2
    dsimp only [j, ji]
    rw [hQleft _ _ (by linarith [hr.1])]
    have he : L * (2 + (N.coordinate_inverse x).2 / L - 2) =
        (N.coordinate_inverse x).2 := by field_simp [hL.ne']; ring
    rw [he]
    exact N.coordinate_map_inverse hx
  have hjs : ContMDiffOn 𝓘(ℝ, E) (𝓡 3) ∞ j A :=
    N.coordinate_map_smooth.comp
      ((contMDiff_fst.comp_contMDiffOn (hQi.mono hAQt)).prodMk
        (contMDiffOn_const.mul
          ((contMDiff_snd.comp_contMDiffOn (hQi.mono hAQt)).sub contMDiffOn_const)))
      hJcoord
  have hjis : ContMDiffOn (𝓡 3) 𝓘(ℝ, E) ∞ ji N.carrier := by
    apply hQ.comp_contMDiffOn
    simpa only [Function.comp_def, div_eq_mul_inv, Pi.add_def, Pi.mul_def] using
      (contMDiff_fst.comp_contMDiffOn N.coordinate_inverse_smooth).prodMk
        (contMDiffOn_const.add
          ((contMDiff_snd.comp_contMDiffOn N.coordinate_inverse_smooth).mul
            contMDiffOn_const))
  let J : OpenPartialHomeomorph E M := {
    toFun := j
    invFun := ji
    source := A
    target := N.carrier
    map_source' := hj
    map_target' := hji
    left_inv' := hjleft
    right_inv' := hjright
    open_source := hAo
    open_target := N.carrier_open
    continuousOn_toFun := hjs.continuousOn
    continuousOn_invFun := hjis.continuousOn }
  have hJformula (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ioo (-L) L) :
      J (Q (q, 2 + t / L)) = N.coordinate_map (q, t) := by
    change N.coordinate_map
      ((Q.symm (Q (q, 2 + t / L))).1, L * ((Q.symm (Q (q, 2 + t / L))).2 - 2)) = _
    rw [hQleft q _ (by have hr := hrad t ht; linarith [hr.1])]
    congr 1
    apply Prod.ext
    · rfl
    · change L * (2 + t / L - 2) = t
      field_simp [hL.ne']
      ring
  let QP := (OpenPartialHomeomorph.refl ℝ).prod Q
  have hQP : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ × E) ∞ QP :=
    contMDiff_fst.prodMk_space (hQ.comp contMDiff_snd)
  have hQPi : ContMDiffOn 𝓘(ℝ, ℝ × E)
      (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ, ℝ))) ∞ QP.symm QP.target :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (hQi.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hp => hp.2))
  have hv : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun q => rd - rh q) :=
    contMDiff_const.sub hrhs
  have hshift : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, ℝ) ∞ (fun p : ℝ × RoundCylinderSpace => p.1 * (rd - rh p.2.1)) :=
    contMDiff_fst.mul (hv.comp (contMDiff_fst.comp contMDiff_snd))
  let T : Diffeomorph (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ, ℝ)))
      (𝓘(ℝ, ℝ).prod ((𝓡 2).prod 𝓘(ℝ, ℝ)))
      (ℝ × RoundCylinderSpace) (ℝ × RoundCylinderSpace) ∞ := {
    toFun := fun p => (p.1, p.2.1, p.2.2 + p.1 * (rd - rh p.2.1))
    invFun := fun p => (p.1, p.2.1, p.2.2 - p.1 * (rd - rh p.2.1))
    left_inv := fun p => Prod.ext rfl (Prod.ext rfl (add_sub_cancel_right _ _))
    right_inv := fun p => Prod.ext rfl (Prod.ext rfl (sub_add_cancel _ _))
    contMDiff_toFun := contMDiff_fst.prodMk
      ((contMDiff_fst.comp contMDiff_snd).prodMk
        ((contMDiff_snd.comp contMDiff_snd).add hshift))
    contMDiff_invFun := contMDiff_fst.prodMk
      ((contMDiff_fst.comp contMDiff_snd).prodMk
        ((contMDiff_snd.comp contMDiff_snd).sub hshift)) }
  let G0 := (QP.symm.transHomeomorph T.toHomeomorph).trans QP
  have hG0 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) ∞ G0 G0.source :=
    hQP.comp_contMDiffOn ((T.contMDiff.comp_contMDiffOn hQPi).mono inter_subset_left)
  have hG0i : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) ∞ G0.symm G0.target :=
    hQP.comp_contMDiffOn (T.symm.contMDiff.comp_contMDiffOn
      (hQPi.mono inter_subset_left))
  let O : Set (ℝ × E) := univ ×ˢ A
  have hOo : IsOpen O := isOpen_univ.prod hAo
  let G := (G0.restrOpen O hOo).trans (OpenPartialHomeomorph.ofSet O hOo)
  have hGs : G.source ⊆ G0.source := fun _ hp => hp.1.1
  have hGt : G.target ⊆ G0.target := fun _ hp => hp.2.1
  have hGA : Prod.snd '' G.target ⊆ A := by
    rintro x ⟨p, hp, rfl⟩
    exact hp.1.2
  have hGformula (p : ℝ × E) : G p =
      (p.1, Q ((Q.symm p.2).1, (Q.symm p.2).2 + p.1 * (rd - rh (Q.symm p.2).1))) := rfl
  have hGtrack (t : ℝ) (q : UnitTwoSphere) :
      G (t, Q (q, rh q)) = (t, Q (q, rh q + t * (rd - rh q))) := by
    rw [hGformula, hQleft q _ (by linarith [(hrh q).1])]
  have hGmem (t : ℝ) (q : UnitTwoSphere)
      (ht : rh q + t * (rd - rh q) ∈ Ioo (1 : ℝ) 3) : (t, Q (q, rh q)) ∈ G.source := by
    have hqpos : 0 < rh q := by linarith [(hrh q).1]
    have hnewpos : 0 < rh q + t * (rd - rh q) := by linarith [ht.1]
    refine ⟨⟨?_, ⟨mem_univ _, hQA q (hrh q)⟩⟩, ?_⟩
    · refine ⟨⟨mem_univ _, Q.map_source (hQs.symm ▸ ⟨mem_univ _, hqpos⟩)⟩, ?_⟩
      change (t, (Q.symm (Q (q, rh q))).1,
        (Q.symm (Q (q, rh q))).2 + t * (rd - rh (Q.symm (Q (q, rh q))).1)) ∈
          univ ×ˢ Q.source
      rw [hQleft q _ hqpos, hQs]
      exact ⟨mem_univ _, mem_univ _, hnewpos⟩
    · change G (t, Q (q, rh q)) ∈ O
      rw [hGtrack]
      exact ⟨mem_univ _, hQA q ht⟩
  let Gamma : Set E := range (fun q : UnitTwoSphere => Q (q, rh q))
  have hGamma : IsCompact Gamma :=
    isCompact_range (hQ.continuous.comp (continuous_id.prodMk hrhs.continuous))
  have htracks : Icc (0 : ℝ) 1 ×ˢ Gamma ⊆ G.source := by
    rintro ⟨t, x⟩ ⟨ht, ⟨q, rfl⟩⟩
    apply hGmem
    have hc := convex_Ioo (𝕜 := ℝ) (1 : ℝ) 3 (hrh q) hrd
      (sub_nonneg.mpr ht.2) ht.1 (by ring : (1 - t) + t = 1)
    have he : rh q + t * (rd - rh q) = (1 - t) * rh q + t * rd := by ring
    rw [he]
    exact hc
  obtain ⟨Ot, Ox, hOt, _, htime, hspace, hprod⟩ :=
    generalized_tube_lemma isCompact_Icc hGamma G.open_source htracks
  obtain ⟨r0, hr0, hball0⟩ := Metric.mem_nhds_iff.mp
    (hOt.mem_nhds (htime (show (0 : ℝ) ∈ Icc 0 1 by norm_num)))
  obtain ⟨r1, hr1, hball1⟩ := Metric.mem_nhds_iff.mp
    (hOt.mem_nhds (htime (show (1 : ℝ) ∈ Icc 0 1 by norm_num)))
  let delta := min r0 r1 / 2
  have hdelta : 0 < delta := div_pos (lt_min hr0 hr1) (by norm_num)
  have hd0 : delta < r0 := by dsimp [delta]; linarith [min_le_left r0 r1]
  have hd1 : delta < r1 := by dsimp [delta]; linarith [min_le_right r0 r1]
  have hclosed : Icc (-delta) (1 + delta) ×ˢ Gamma ⊆ G.source := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    apply hprod
    refine ⟨?_, hspace hx⟩
    by_cases ht0 : 0 ≤ t
    · by_cases ht1 : t ≤ 1
      · exact htime ⟨ht0, ht1⟩
      · apply hball1
        change dist t 1 < r1
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith [ht.2]
    · apply hball0
      change dist t 0 < r0
      rw [Real.dist_eq, sub_zero, abs_of_neg (lt_of_not_ge ht0)]
      linarith [ht.1]
  obtain ⟨Phi, _, _, htrack, ⟨C, hC, hCt, hfix⟩, _⟩ :=
    M25.Topology3D.exists_ambient_isotopy_of_chart G
      (hG0.mono hGs).contDiffOn (hG0i.mono hGt).contDiffOn (fun _ _ => rfl)
      (0 : E →L[ℝ] ℝ) (by intro p hp; rfl) hGamma
      (s := 0) (a := -delta) (b := 1 + delta) ⟨by linarith, by linarith⟩ hclosed
  let F := Phi 1
  have hCA : C ⊆ A := hCt.trans hGA
  have hFgraph (q : UnitTwoSphere) : F (Q (q, rh q)) = Q (q, rd) := by
    have ht := htrack (Q (q, rh q)) (show Q (q, rh q) ∈ Gamma from ⟨q, rfl⟩)
      1 ⟨by linarith, by linarith⟩
    rw [hGtrack, hGtrack] at ht
    have he : rh q + 1 * (rd - rh q) = rd := by ring
    simpa only [zero_mul, add_zero, he] using ht
  have hFfix (x : E) (hx : x ∉ C) : F x = x := hfix 1 x hx
  have hFifix (x : E) (hx : x ∉ C) : F.symm x = x := by
    apply F.injective
    change F (F.symm x) = F x
    rw [F.apply_symm_apply, hFfix x hx]
  have hpres (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
      (hD : ∀ x, x ∉ C → D x = x) : MapsTo D A A := by
    intro x hx
    by_cases hy : D x ∈ C
    · exact hCA hy
    · have he : D x = x := D.injective (hD (D x) hy)
      exact he.symm ▸ hx
  have hFA := hpres F hFfix
  have hFiA := hpres F.symm hFifix
  let K : Set M := J '' C
  have hK : IsCompact K := hC.image_of_continuousOn (J.continuousOn.mono hCA)
  have hKN : K ⊆ N.carrier := by
    rintro x ⟨y, hy, rfl⟩
    exact J.map_source (hCA hy)
  let patch : (E → E) → M → M := fun D x =>
    if x ∈ N.carrier then J (D (J.symm x)) else x
  have hpatch (D : E → E) (x : M) (hx : x ∈ N.carrier) :
      patch D x = J (D (J.symm x)) := if_pos hx
  have hpatchmem (D : E → E) (hDA : MapsTo D A A) {x : M} (hx : x ∈ N.carrier) :
      patch D x ∈ N.carrier := by
    rw [hpatch D x hx]
    exact J.map_source (hDA (J.map_target hx))
  have hpatchfix (D : E → E) (hD : ∀ x, x ∉ C → D x = x)
      {x : M} (hx : x ∉ K) : patch D x = x := by
    by_cases hn : x ∈ N.carrier
    · rw [hpatch D x hn, hD _ (fun hy => hx ⟨J.symm x, hy, J.right_inv hn⟩)]
      exact J.right_inv hn
    · exact if_neg hn
  have hpatchsmooth (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
      (hDA : MapsTo D A A) (hD : ∀ x, x ∉ C → D x = x) :
      ContMDiff (𝓡 3) (𝓡 3) ∞ (patch D) := by
    apply contMDiff_of_locally_contMDiffOn
    intro x
    by_cases hn : x ∈ N.carrier
    · refine ⟨N.carrier, N.carrier_open, hn, ?_⟩
      exact (hjs.comp (D.contMDiff.comp_contMDiffOn hjis)
        (fun y hy => hDA (J.map_target hy))).congr (fun y hy => hpatch D y hy)
    · refine ⟨Kᶜ, hK.isClosed.isOpen_compl, fun hx => hn (hKN hx), ?_⟩
      exact contMDiff_id.contMDiffOn.congr (fun y hy => hpatchfix D hD hy)
  have hpatchinv (D D' : E → E) (hDA : MapsTo D A A)
      (hDD : ∀ x, D' (D x) = x) (x : M) : patch D' (patch D x) = x := by
    by_cases hn : x ∈ N.carrier
    · rw [hpatch D' _ (hpatchmem D hDA hn), hpatch D x hn,
        J.left_inv (hDA (J.map_target hn)), hDD, J.right_inv hn]
    · simp only [patch, if_neg hn]
  let Psi : Diffeomorph (𝓡 3) (𝓡 3) M M ∞ := {
    toFun := patch F
    invFun := patch F.symm
    left_inv := hpatchinv F F.symm hFA F.symm_apply_apply
    right_inv := hpatchinv F.symm F hFiA F.apply_symm_apply
    contMDiff_toFun := hpatchsmooth F hFA hFfix
    contMDiff_invFun := hpatchsmooth F.symm hFiA hFifix }
  have hPsigraph (q : UnitTwoSphere) :
      Psi (N.coordinate_map (q, h q)) = N.coordinate_map (q, d) := by
    have hx := N.coordinate_map_mem (z := (q, h q)) ⟨mem_univ q, hdom q⟩
    change patch F (N.coordinate_map (q, h q)) = _
    rw [hpatch F _ hx]
    have hiq : J.symm (N.coordinate_map (q, h q)) = Q (q, rh q) := by
      rw [← hJformula q (h q) (hdom q)]
      exact J.left_inv (hQA q (hrh q))
    rw [hiq, hFgraph]
    exact hJformula q d hd
  refine ⟨Psi, ⟨K, hK, hKN, fun x hx => hpatchfix F hFfix hx⟩, ?_⟩
  rw [← range_comp']
  exact congrArg range (funext hPsigraph)

end PoincareConjecture
