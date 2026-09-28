import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ComponentDiameter.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.Level.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient.Flow.LevelEvolution

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Topology Filter
open Poincare.Geometry.Riemannian.ScalarOperators.Gradient.Flow
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem local_flow_cancel
    {X : (x : M) → TangentSpace (𝓡 n) x} {O V : Set M} (hO : IsOpen O)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) 1 (T% X) O)
    {δ : ℝ} (hδ : 0 < δ) {Φ : ℝ × M → M}
    (hinit : ∀ y ∈ V, Φ (0, y) = y)
    (horbit : ∀ y ∈ V, (∀ t ∈ Ioo (-δ) δ, Φ (t, y) ∈ O) ∧
      IsMIntegralCurveOn (I := 𝓡 n) (fun t => Φ (t, y)) X (Ioo (-δ) δ))
    {x : M} (hx : x ∈ V) {t : ℝ} (ht : t ∈ Ioo (-δ) δ)
    (htx : Φ (t, x) ∈ V) : Φ (-t, Φ (t, x)) = x := by
  let J := Ioo (-δ) δ ∩ (fun s : ℝ => s + t) ⁻¹' Ioo (-δ) δ
  have hJ : IsOpen J := isOpen_Ioo.inter
    (isOpen_Ioo.preimage (continuous_id.add continuous_const))
  have hpre : (fun s : ℝ => s + t) ⁻¹' Ioo (-δ) δ = Ioo (-δ-t) (δ-t) := by
    ext s
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hJc : IsPreconnected J := by
    dsimp only [J]
    rw [hpre]
    exact ((convex_Ioo (-δ) δ).inter (convex_Ioo (-δ-t) (δ-t))).isPreconnected
  have hz : (0 : ℝ) ∈ J := ⟨⟨by linarith, hδ⟩, by simpa using ht⟩
  have hneg : -t ∈ J := ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩,
    by change -t+t ∈ Ioo (-δ) δ; rw [neg_add_cancel]; exact ⟨by linarith, hδ⟩⟩
  have heq := Poincare.Manifold.eqOn_of_isMIntegralCurveOn hO hX hJ hJc hz
    (fun s hs => (horbit x hx).1 (s + t) hs.2)
    (((horbit x hx).2.comp_add t).mono inter_subset_right)
    ((horbit _ htx).2.mono inter_subset_left)
    (by simpa only [zero_add] using (hinit _ htx).symm)
  simpa only [neg_add_cancel, hinit x hx] using (heq hneg).symm

theorem exists_collar_of_compact_regular_level
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {O : Set M} (hO : IsOpen O)
    (hreg : ∀ x ∈ O, mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x ≠ 0)
    (a : ℝ) (hK : IsCompact {x | x ∈ O ∧ f x = a}) :
    ∃ (s : ℝ) (hs : 0 < s) (U : Set M), IsOpen U ∧ U ⊆ O ∧
      ∃ e : ({x | x ∈ O ∧ f x = a} × Ioo (-s) s) ≃ₜ U,
        ∀ x, (e (x, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M) = x := by
  let K := {x | x ∈ O ∧ f x = a}
  have hband : IsCompact {x | x ∈ O ∧ f x ∈ Icc a a} := by
    simpa only [Icc_self, mem_singleton_iff] using hK
  obtain ⟨V, δ, Φ, hV, hKV, hVO, hδ, hΦ, hinit, horbit, _⟩ :=
    D.exists_normalizedGradient_flow_on_compact_regular_band hf hO hreg hband hK
      (fun _ hx => hx.1) (T := 0) le_rfl (fun _ hx => hx.2.ge)
      (fun _ hx => by rw [hx.2]; simp)
  simp only [zero_add] at hΦ horbit
  have hz : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hX := (D.contMDiffOn_normalizedGradient_of_regular hO hf.contMDiffOn hreg).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hscalar (x : M) (hx : x ∈ V) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      f (Φ (t, x)) = f x + t := by
    have hh := D.comp_normalizedGradient_eq_add_on isOpen_Ioo isPreconnected_Ioo
      (fun t _ => (hf _).mdifferentiableAt (by simp))
      (fun t ht => fun he => hreg _ ((horbit x hx).1 t ht)
        ((gradient_energy_eq_zero_iff_mfderiv_eq_zero_manifold D f _).mp he))
      (horbit x hx).2 hz ht
    simpa only [hinit x hx, sub_zero] using hh
  let A := (Ioo (-δ) δ ×ˢ V) ∩ Φ ⁻¹' V
  have hA : IsOpen A := hΦ.continuousOn.isOpen_inter_preimage
    (isOpen_Ioo.prod hV) hV
  have hzero : ({0} : Set ℝ) ×ˢ K ⊆ A := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨hz, hKV hx⟩, by
      change Φ (0, x) ∈ V
      rw [hinit x (hKV hx)]
      exact hKV hx⟩
  obtain ⟨B, W, hB, _, h0B, hKW, hBW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hA hzero
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.mp hB 0 (h0B (mem_singleton 0))
  let s := min r δ / 2
  have hs : 0 < s := half_pos (lt_min hr hδ)
  have hsr : s < r := (half_lt_self (lt_min hr hδ)).trans_le (min_le_left _ _)
  have hsδ : s < δ := (half_lt_self (lt_min hr hδ)).trans_le (min_le_right _ _)
  have hsub : Ioo (-s) s ⊆ Ioo (-δ) δ := Ioo_subset_Ioo (by linarith) hsδ.le
  have hstay (x : K) (t : ℝ) (ht : t ∈ Ioo (-s) s) : Φ (t, x) ∈ V := by
    apply (hBW ⟨hrB ?_, hKW x.property⟩).2
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let U := V ∩ f ⁻¹' Ioo (a-s) (a+s)
  have hU : IsOpen U := hV.inter (isOpen_Ioo.preimage hf.continuous)
  have htU (y : U) : f y - a ∈ Ioo (-s) s :=
    ⟨by linarith [y.property.2.1], by linarith [y.property.2.2]⟩
  have hbU (y : U) : a - f y ∈ Ioo (-δ) δ := by
    apply hsub
    exact ⟨by linarith [(htU y).2], by linarith [(htU y).1]⟩
  have hback (y : U) : Φ (a-f y, y) ∈ K := by
    refine ⟨(horbit y y.property.1).1 _ (hbU y), ?_⟩
    rw [hscalar y y.property.1 _ (hbU y)]
    ring
  let F : (K × Ioo (-s) s) → U := fun z =>
    ⟨Φ (z.2, z.1), hstay z.1 z.2 z.2.property, by
      change f (Φ (z.2, z.1)) ∈ Ioo (a-s) (a+s)
      rw [hscalar z.1 (hKV z.1.property) z.2 (hsub z.2.property), z.1.property.2]
      exact ⟨by linarith [z.2.property.1], by linarith [z.2.property.2]⟩⟩
  let G : U → (K × Ioo (-s) s) := fun y =>
    (⟨Φ (a-f y, y), hback y⟩, ⟨f y-a, htU y⟩)
  have hGF : Function.LeftInverse G F := by
    rintro ⟨x, t⟩
    have hval := hscalar x (hKV x.property) t (hsub t.property)
    rw [x.property.2] at hval
    apply Prod.ext
    · apply Subtype.ext
      change Φ (a-f (Φ (t, x)), Φ (t, x)) = x
      rw [hval, show a - (a + (t : ℝ)) = -t by ring]
      exact local_flow_cancel hO hX hδ hinit horbit (hKV x.property)
        (hsub t.property) (hstay x t t.property)
    · apply Subtype.ext
      change f (Φ (t, x)) - a = t
      rw [hval]
      ring
  have hFG : Function.RightInverse G F := by
    intro y
    apply Subtype.ext
    change Φ (f y-a, Φ (a-f y, y)) = y
    have hh := local_flow_cancel hO hX hδ hinit horbit y.property.1 (hbU y)
      (hKV (hback y))
    simpa only [neg_sub] using hh
  have hFc : Continuous F := by
    apply Continuous.subtype_mk
    apply hΦ.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst))
    exact fun z => ⟨hsub z.2.property, hKV z.1.property⟩
  have hGc : Continuous G := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      apply hΦ.continuousOn.comp_continuous
        ((continuous_const.sub (hf.continuous.comp continuous_subtype_val)).prodMk
          continuous_subtype_val)
      exact fun y => ⟨hbU y, y.property.1⟩
    · exact ((hf.continuous.comp continuous_subtype_val).sub continuous_const).subtype_mk _
  refine ⟨s, hs, U, hU, inter_subset_left.trans hVO,
    ⟨⟨F, G, hGF, hFG⟩, hFc, hGc⟩, ?_⟩
  intro x
  exact hinit x (hKV x.property)

end PoincareConjecture.LeviCivitaData
