import PoincareConjecture.Proofs.M25.Topology3D.Plane.FixedTailInscribedPolygon
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ArcRelativeStraightening
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcAffineTransport
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedOpenLineTube
import PoincareConjecture.Proofs.M25.Topology3D.Plane.PositiveOpenLineTransport

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_axis_preserving_correction_of_slide
    (F : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hline : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 (p.2, 0)))
    (hinj : ∀ z, Injective (fun u : ℝ => F z (u, 0)))
    (hreg : ∀ z u : ℝ, deriv (fun s => F z (s, 0)) u ≠ 0)
    {Q : Set (ℝ × ℝ)} (hQ : IsCompact Q) (hQfix : ∀ z x, x ∉ Q → F z x = x)
    (hends : ∀ z, z ≤ 1 / 3 ∨ 2 / 3 ≤ z → ∀ u : ℝ, F z (u, 0) = (u, 0)) :
    ∃ G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) ∧
      (∃ S : Set (ℝ × ℝ), IsCompact S ∧ ∀ z x, x ∉ S → G z x = x) ∧
      (∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x, G z x = x) ∧
      ∀ z u : ℝ, (G z (F z (u, 0))).2 = 0 := by
  obtain ⟨R, hR, hbound⟩ := hQ.isBounded.exists_pos_norm_lt
  let C : ℝ × ℝ → ℝ × ℝ := fun p => F p.1 (p.2, 0)
  have hC : ContDiff ℝ ∞ C := hline
  have hCi (t : ℝ) : Injective (fun u : ℝ => C (t, u)) := hinj t
  have hCr (t u : ℝ) : fderiv ℝ (fun v : ℝ => C (t, v)) u 1 ≠ 0 := by
    simpa only [C, fderiv_apply_one_eq_deriv] using hreg t u
  have hCt (t u : ℝ) (hu : R ≤ |u|) : C (t, u) = (u, 0) := by
    apply hQfix
    intro huQ
    have hb := (norm_fst_le ((u, 0) : ℝ × ℝ)).trans_lt (hbound (u, 0) huQ)
    change ‖u‖ < R at hb
    rw [Real.norm_eq_abs] at hb
    exact (not_lt_of_ge hu) hb
  have hCa (t : ℝ) (ht : t ≤ 1 / 6 ∨ 5 / 6 ≤ t) (u : ℝ) : C (t, u) = (u, 0) := by
    apply hends
    exact ht.imp (fun h => by linarith) (fun h => by linarith)
  have hCs (t : ℝ) (ht : t ≤ 0 ∨ 1 ≤ t) (u : ℝ) : C (t, u) = (u, 0) :=
    hCa t (ht.imp (fun h => by linarith) (fun h => by linarith)) u
  let C0 : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun p => C (p.1.1, p.2)
  have hC0 : ContDiff ℝ ∞ C0 := hC.comp (contDiff_fst.fst.prodMk contDiff_snd)
  let K0 : Set (ℝ × ℝ) := Icc (-1 : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1
  obtain ⟨e, he, _, w, hw, _, T, hTs, hTf, hT, hInv, _⟩ :=
    exists_fixedTail_openLine_normalTube C0 (a := -1) (b := 2) (c := -1) (d := 1)
      (by norm_num) (by norm_num) hR hC0 (fun z _ => hCi z.1)
      (fun z _ u => hCr z.1 u) (fun z u hu => hCt z.1 u hu)
  let U : Set (ℝ × ℝ) := Ioo (-1 - e) (2 + e) ×ˢ Ioo (-1 - e) (1 + e)
  have hK0U : K0 ⊆ U := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hzero (z : ℝ × ℝ) (u : ℝ) : T (z, (u, 0)) = (z, C0 (z, u)) := by
    simpa only [zero_smul, add_zero] using hTf (z, (u, 0))
  have hsrc (z : ℝ × ℝ) (hz : z ∈ K0) (u : ℝ) : (z, (u, (0 : ℝ))) ∈ T.source := by
    rw [hTs]
    exact ⟨hK0U hz, by simpa using hw⟩
  have htarget (z : ℝ × ℝ) (hz : z ∈ K0) (u : ℝ) : (z, C0 (z, u)) ∈ T.target := by
    rw [← hzero]
    exact T.map_source (hsrc z hz u)
  have hrecover (z : ℝ × ℝ) (hz : z ∈ K0) (u : ℝ) :
      T.symm (z, C0 (z, u)) = (z, (u, 0)) := by
    rw [← hzero]
    exact T.left_inv (hsrc z hz u)
  obtain ⟨η, hη, _, hcertificate⟩ :=
    exists_uniform_rounded_openLine_tube_certificate C0 hC0 hR
      (fun z u hu => hCt z.1 u hu) T hInv (isCompact_Icc.prod isCompact_Icc)
      htarget hrecover (half_pos hw)
  obtain ⟨n, r, hRr, m, hm, hm0, hml, hmform, hsmall, P, hP, hPg⟩ :=
    exists_fixedTail_openLine_inscribed_polygon_fine C hR hη hC hCi hCr hCt hCs
  have hr : 0 < r := hR.trans hRr
  let h : ℝ := 2 * r / (n + 2)
  have hh : 0 < h := by dsimp [h]; positivity
  have hmeshEnd : -r + h * ((n + 1 + 1 : ℕ) : ℝ) = r := by
    dsimp [h]
    push_cast
    field_simp
    ring
  have hmf (j : Fin (n + 3)) : m j = -r + h * (j.val : ℝ) := by
    rw [hmform]
    dsimp [h]
    ring
  have hPs (j : Fin (n + 3)) : ContDiff ℝ ∞ (fun t => P t j) := by
    have heq : (fun t => P t j) = fun t => C (t, m j) := funext (fun t => hP t j)
    rw [heq]
    exact hC.comp (contDiff_id.prodMk contDiff_const)
  have hmI (j : Fin (n + 3)) : m j ∈ Icc (-r) r := by
    rw [← hm0, ← hml]
    exact ⟨hm.monotone (Fin.zero_le j), hm.monotone (Fin.le_last j)⟩
  have hmseg (j : Fin (n + 3)) : (m j, 0) ∈
      segment ℝ ((-r, 0) : ℝ × ℝ) ((r, 0) : ℝ × ℝ) := by
    have hi : m j ∈ segment ℝ (-r) r := by
      rw [segment_eq_Icc (by linarith : -r ≤ r)]
      exact hmI j
    have hi' := mem_image_of_mem (LinearMap.inl ℝ ℝ ℝ).toAffineMap hi
    rw [image_segment] at hi'
    simpa only [LinearMap.coe_toAffineMap, LinearMap.inl_apply] using hi'
  have hPaxis (t : ℝ) (ht : t ≤ 1 / 6 ∨ 5 / 6 ≤ t) (j : Fin (n + 3)) :
      P t j = (m j, 0) := (hP t j).trans (hCa t ht (m j))
  have hflat0 (t : ℝ) (ht : |t| < 1 / 6) (j : Fin (n + 3)) :
      P t j ∈ segment ℝ ((-r, 0) : ℝ × ℝ) ((r, 0) : ℝ × ℝ) := by
    rw [hPaxis t (Or.inl (abs_lt.mp ht).2.le) j]
    exact hmseg j
  have hflat1 (t : ℝ) (ht : |t - 1| < 1 / 6) (j : Fin (n + 3)) :
      P t j ∈ segment ℝ ((-r, 0) : ℝ × ℝ) ((r, 0) : ℝ × ℝ) := by
    rw [hPaxis t (Or.inr (by linarith [(abs_lt.mp ht).1])) j]
    exact hmseg j
  obtain ⟨ν, hν, _, Φ, hΦs, hΦg, hΦ0, _, hΦtail, hΦflat⟩ :=
    exists_relative_polygonalArc_straightening (E := ℝ × ℝ) (by simp) (n + 1)
      (-r, 0) (r, 0) (LinearMap.fst ℝ ℝ ℝ) (by change -r < r; linarith)
      P hPs hPg (by norm_num : 0 < (1 / 6 : ℝ)) (by norm_num) hflat0 hflat1
  have hΦmesh (s t : ℝ) (ht : t ≤ 0 ∨ 1 ≤ t) (j : Fin (n + 3)) :
      Φ (s, t) j = (-r + h * (j.val : ℝ), 0) := by
    rw [hΦtail s t (ht.imp (fun ht => ht.trans hν.le) (fun ht => by linarith)),
      hP, hCs t ht, hmf]
  have hΦaxis (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : Fin (n + 3)) :
      (Φ (1, t) j).2 = 0 := by
    have hx := mem_image_of_mem (LinearMap.snd ℝ ℝ ℝ).toAffineMap (hΦflat t ht j)
    rw [image_segment] at hx
    simpa using hx
  obtain ⟨δ, hδ, hδquarter, ρ, hρ, hρtail, hρbound, hρder,
      J, hJ, _, ⟨QJ, hQJ, hJfix⟩, hJends, hJaxis⟩ :=
    exists_affine_rounded_openArc_transport (n := n + 1) (-r) h hh Φ hΦs
      (fun s _ t _ => by simpa only [hmeshEnd, LinearMap.fst_apply] using hΦg s t)
      hΦmesh hΦaxis
  let γ : (ℝ × ℝ) × ℝ → ℝ × ℝ := fun p =>
    roundedVertexPath ρ (fun i : ℤ => C0 (p.1, -r + h * i)) ((p.2 - -r) / h)
  obtain ⟨hγ, hγtail, hγid, hγtube⟩ :=
    hcertificate (-r) h hh hsmall δ hδ (by linarith) ρ hρ hρtail hρbound hρder
  change ContDiff ℝ ∞ γ at hγ
  have hsample (t u : ℝ) :
      affineRoundedOpenArcParameter ρ (-r) h (Φ (0, t)) u = γ ((t, 0), u) := by
    apply affineRoundedOpenArcParameter_eq_samples hh (fun v => C (t, v))
      (Φ (0, t)) (by linarith) (by rw [hmeshEnd]; exact hRr.le) (hCt t)
    intro j
    rw [hΦ0 0 t le_rfl, hP, hmf]
  let V : Set (ℝ × ℝ) := Ioo (-1 / 2 : ℝ) (3 / 2) ×ˢ Ioo (-1 / 2 : ℝ) (1 / 2)
  let K : Set (ℝ × ℝ) := Icc (-1 / 4 : ℝ) (5 / 4) ×ˢ Icc (-1 / 4 : ℝ) (1 / 4)
  have hVK0 : V ⊆ K0 := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hKV : K ⊆ V := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hnear (z : ℝ × ℝ) (hz : z ∈ V) (u : ℝ) :
      (z, γ (z, u)) ∈ T.target ∧
        0 < fderiv ℝ (fun p : (ℝ × ℝ) × ℝ => (T.symm (p.1, γ p)).2.1)
          (z, u) (0, 1) ∧ |(T.symm (z, γ (z, u))).2.2| < w / 2 := by
    obtain ⟨hmem, hpos, hheight⟩ := hγtube z (hVK0 hz) u
    refine ⟨hmem, ?_, hheight⟩
    let L : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun p => (T.symm p).2.1
    have hL : DifferentiableAt ℝ L (z, γ (z, u)) :=
      (hInv.snd.fst.contDiffAt (T.open_target.mem_nhds hmem)).differentiableAt (by simp)
    have harg : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => (p.1, γ p)) :=
      contDiff_fst.prodMk hγ
    have hcomp := hL.comp (z, u) (harg.differentiable (by simp) (z, u))
    have hd1 := hasDerivAt_fiber hcomp.hasFDerivAt
    have hslice : HasDerivAt (fun v : ℝ => γ (z, v))
        (deriv (fun v : ℝ => γ (z, v)) u) u :=
      ((hγ.comp (contDiff_const.prodMk contDiff_id)).differentiable
        (by simp) u).hasDerivAt
    have hd2 := hL.hasFDerivAt.comp_hasDerivAt u ((hasDerivAt_const u z).prodMk hslice)
    have heq := hd1.unique (by simpa only [Function.comp_def] using hd2)
    change 0 < fderiv ℝ (L ∘ fun p : (ℝ × ℝ) × ℝ => (p.1, γ p)) (z, u) (0, 1)
    rw [heq]
    exact hpos
  have htailInv (z : ℝ × ℝ) (hz : z ∈ V) (u : ℝ) (hu : R + 2 ≤ |u|) :
      T.symm (z, γ (z, u)) = (z, (u, 0)) := by
    have hγC : γ (z, u) = C0 (z, u) :=
      (hγtail z u hu).trans (hCt z.1 u (by linarith)).symm
    rw [hγC]
    exact hrecover z (hVK0 hz) u
  obtain ⟨τt, hτt, hτtb, hτt1, hτt0⟩ :=
    exists_smooth_interval_cutoff 0 1 (by norm_num : 0 < (1 / 4 : ℝ))
  obtain ⟨τs, hτs, hτsb, hτs1, hτs0⟩ :=
    exists_smooth_interval_cutoff 0 0 (by norm_num : 0 < (1 / 4 : ℝ))
  let τ : ℝ × ℝ → ℝ := fun z => τt z.1 * τs z.2
  have hτ : ContDiff ℝ ∞ τ := (hτt.comp contDiff_fst).mul (hτs.comp contDiff_snd)
  have hτbound (z : ℝ × ℝ) : 0 ≤ τ z ∧ τ z ≤ 1 := by
    refine ⟨mul_nonneg (hτtb z.1).1 (hτsb z.2).1, ?_⟩
    dsimp only [τ]
    nlinarith [(hτtb z.1).1, (hτtb z.1).2, (hτsb z.2).1, (hτsb z.2).2]
  have houtside {l b x : ℝ} (hx : x ∉ Icc l b) : x ≤ l ∨ b ≤ x := by
    by_cases hl : l ≤ x
    · exact Or.inr (le_of_not_gt (fun ht => hx ⟨hl, ht.le⟩))
    · exact Or.inl (lt_of_not_ge hl).le
  have hτzero (z : ℝ × ℝ) (hz : z ∉ K) : τ z = 0 := by
    by_cases ht : z.1 ∈ Icc (-1 / 4 : ℝ) (5 / 4)
    · have hs : z.2 ∉ Icc (-1 / 4 : ℝ) (1 / 4) := fun hs => hz ⟨ht, hs⟩
      have hzeroS : τs z.2 = 0 := hτs0 z.2 (by
        rcases houtside hs with hs | hs
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith))
      simp only [τ, hzeroS, mul_zero]
    · have hzeroT : τt z.1 = 0 := hτt0 z.1 (by
        rcases houtside ht with ht | ht
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith))
      simp only [τ, hzeroT, zero_mul]
  obtain ⟨I, hI, _, ⟨QI, hQI, hIfix⟩, _, hIstat, hIrange⟩ :=
    exists_positive_openLine_graph_transport T (isOpen_Ioo.prod isOpen_Ioo)
      (fun z hz => hK0U (hVK0 hz)) (isCompact_Icc.prod isCompact_Icc) hKV
      (half_pos hw) (by linarith) (by linarith : 0 < R + 2) hTs
      (fun p => by rw [hTf]) hT hInv γ hγ hnear htailInv
      τ hτ hτbound hτzero
  have hIends (t : ℝ) (ht : t ≤ 0 ∨ 1 ≤ t) (x : ℝ × ℝ) : I (t, 0) x = x := by
    apply (hIstat (t, 0) ?_ x).1
    intro u
    rw [hzero]
    change γ ((t, 0), u) = C (t, u)
    rw [hCs t ht]
    exact hγid (t, 0) (hCs t ht) u
  have hrange (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      range (fun u : ℝ => I (t, 0) (C (t, u))) = range (fun u : ℝ => γ ((t, 0), u)) := by
    have hVt : (t, (0 : ℝ)) ∈ V :=
      ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, by norm_num⟩
    have hτone : τ (t, 0) = 1 := by
      simp only [τ, hτt1 t ht, hτs1 0 (by simp), one_mul]
    simpa only [hzero, C0] using hIrange (t, 0) hVt hτone
  let G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := fun t => (I (t, 0)).trans (J t)
  have hIs : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => I (p.1, 0) p.2) :=
    hI.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
  have hG : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) :=
    hJ.comp (contDiff_fst.prodMk hIs)
  have hGends (t : ℝ) (ht : t ≤ 0 ∨ 1 ≤ t) (x : ℝ × ℝ) : G t x = x := by
    change J t (I (t, 0) x) = x
    rw [hIends t ht, (hJends t ht x).1]
  refine ⟨G, hG, ⟨QI ∪ QJ, hQI.union hQJ, ?_⟩, hGends, ?_⟩
  · intro t x hx
    change J t (I (t, 0) x) = x
    rw [(hIfix (t, 0) x (fun h => hx (Or.inl h))).1,
      (hJfix t x (fun h => hx (Or.inr h))).1]
  · intro t u
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · have hmem : I (t, 0) (C (t, u)) ∈ range (fun v : ℝ => γ ((t, 0), v)) := by
        rw [← hrange t ht]
        exact ⟨u, rfl⟩
      obtain ⟨v, hv⟩ := hmem
      change γ ((t, 0), v) = I (t, 0) (C (t, u)) at hv
      change (J t (I (t, 0) (C (t, u)))).2 = 0
      rw [← hv, ← hsample t v]
      exact hJaxis t ht v
    · have ht' : t ≤ 0 ∨ 1 ≤ t := houtside ht
      rw [hGends t ht']
      change (C (t, u)).2 = 0
      rw [hCs t ht']

end PoincareConjecture.M25.Topology3D
