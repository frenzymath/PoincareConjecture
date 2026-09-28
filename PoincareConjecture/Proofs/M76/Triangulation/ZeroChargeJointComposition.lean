import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointSignedCutoff
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]




noncomputable def jointProjectedCutoff
    (F : V × (ℝ × ℝ) → E × ℝ) (j : E → V × ℝ) (R epsilon : ℝ)
    (p : E × ℝ) : E :=
  (F ((j p.1).1, (signedTimeCutoff R epsilon p.2 (j p.1).2, (j p.1).2))).1





theorem jointProjectedCutoff_finitePiecewiseAffineOn
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
    {F : V × (ℝ × ℝ) → E × ℝ} {j : E → V × ℝ}
    {B : Set V} {N : Set E} {J : Set ℝ} {r R epsilon : ℝ}
    (hF : FinitePiecewiseAffineOn F (B ×ˢ (Icc (-r) r ×ˢ J)))
    (hj : FinitePiecewiseAffineOn j N) (hjmap : MapsTo j N (B ×ˢ J))
    (hR : 0 < R) (hepsilon : 0 < epsilon) (hepsr : epsilon ≤ r) :
    FinitePiecewiseAffineOn (jointProjectedCutoff F j R epsilon)
      (N ×ˢ Icc (-epsilon) epsilon) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show -epsilon < epsilon by linarith)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) (Icc (-epsilon) epsilon) :=
    ⟨K, hK, hKI, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have hpair := hj.prodMap hid
  have hp : FinitePiecewiseAffineOn (fun p : E × ℝ => (j p.1).1)
      (N ×ˢ Icc (-epsilon) epsilon) :=
    hpair.postcomp ((ContinuousLinearMap.fst ℝ V ℝ).comp
      (ContinuousLinearMap.fst ℝ (V × ℝ) ℝ)).toContinuousAffineMap
  have hz : FinitePiecewiseAffineOn (fun p : E × ℝ => (j p.1).2)
      (N ×ˢ Icc (-epsilon) epsilon) :=
    hpair.postcomp ((ContinuousLinearMap.snd ℝ V ℝ).comp
      (ContinuousLinearMap.fst ℝ (V × ℝ) ℝ)).toContinuousAffineMap
  have ht : FinitePiecewiseAffineOn (fun p : E × ℝ => p.2)
      (N ×ˢ Icc (-epsilon) epsilon) :=
    hpair.postcomp (ContinuousLinearMap.snd ℝ (V × ℝ) ℝ).toContinuousAffineMap
  have hg := signedTimeCutoff_finitePiecewiseAffineOn ht hz R epsilon
  have hinput := hp.prod_mk (hg.prod_mk hz)
  have hmaps : MapsTo
      (fun p : E × ℝ => ((j p.1).1,
        (signedTimeCutoff R epsilon p.2 (j p.1).2, (j p.1).2)))
      (N ×ˢ Icc (-epsilon) epsilon) (B ×ˢ (Icc (-r) r ×ˢ J)) := by
    intro p hpN
    have hx := hjmap hpN.1
    have htime := signedTimeCutoff_mem hR hepsilon.le p.2 (j p.1).2
    exact ⟨hx.1, ⟨⟨(neg_le_neg hepsr).trans htime.1,
      htime.2.trans hepsr⟩, hx.2⟩⟩
  exact (hF.comp hinput hmaps).postcomp
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] in


theorem jointProjectedCutoff_at_zero
    {F : V × (ℝ × ℝ) → E × ℝ} {j : E → V × ℝ}
    {N : Set E} {R epsilon : ℝ} (hR : 0 < R) (hepsilon : 0 ≤ epsilon)
    (hzero : ∀ x ∈ N, (F ((j x).1, (0, (j x).2))).1 = x)
    {x : E} (hx : x ∈ N) : jointProjectedCutoff F j R epsilon (x, 0) = x := by
  change (F ((j x).1, (signedTimeCutoff R epsilon 0 (j x).2, (j x).2))).1 = x
  rw [signedTimeCutoff_at_zero hR hepsilon]
  exact hzero x hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] in



theorem jointProjectedCutoff_fixed_margin
    {F : V × (ℝ × ℝ) → E × ℝ} {j : E → V × ℝ}
    {N : Set E} {R epsilon : ℝ} (hR : 0 < R) (hepsilon : 0 ≤ epsilon)
    (hzero : ∀ x ∈ N, (F ((j x).1, (0, (j x).2))).1 = x)
    {x : E} (hx : x ∈ N) (hz : R ≤ |(j x).2|) (t : ℝ) :
    jointProjectedCutoff F j R epsilon (x, t) = x := by
  change (F ((j x).1, (signedTimeCutoff R epsilon t (j x).2, (j x).2))).1 = x
  rw [signedTimeCutoff_eq_zero_of_radius_le hR hepsilon t _ hz]
  exact hzero x hx

omit [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] in


theorem jointProjectedCutoff_core
    {F : V × (ℝ × ℝ) → E × ℝ} {j : E → V × ℝ}
    {R epsilon t : ℝ} (hR : 0 < R) (hepsilon : 0 ≤ epsilon)
    (ht : t ∈ Icc (-epsilon) epsilon) {x : E} (hz : (j x).2 = 0) :
    jointProjectedCutoff F j R epsilon (x, t) = (F ((j x).1, (t, 0))).1 := by
  change (F ((j x).1, (signedTimeCutoff R epsilon t (j x).2, (j x).2))).1 = _
  rw [hz, signedTimeCutoff_core hR hepsilon ht]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in





theorem jointProjectedCutoff_injOn
    {F : V × (ℝ × ℝ) → E × ℝ} {j : E → V × ℝ}
    {B : Set V} {N : Set E} {J : Set ℝ} {r R epsilon L : ℝ}
    (hF : InjOn F (B ×ˢ (Icc (-r) r ×ˢ J)))
    (hj : InjOn j N) (hjmap : MapsTo j N (B ×ˢ J))
    (hheight : ∀ p ∈ B ×ˢ (Icc (-r) r ×ˢ J), (F p).2 = p.2.1)
    (hL : 0 ≤ L)
    (htrans : ∀ x ∈ B ×ˢ (Icc (-r) r ×ˢ J),
      ∀ y ∈ B ×ˢ (Icc (-r) r ×ˢ J), |x.2.2 - y.2.2| ≤ L * ‖F x - F y‖)
    (hR : 0 < R) (hepsilon : 0 ≤ epsilon) (hepsr : epsilon ≤ r)
    (hsmall : L * ‖((0 : E), (1 : ℝ))‖ * (epsilon / R) < 1) (t : ℝ) :
    InjOn (fun x => jointProjectedCutoff F j R epsilon (x, t)) N := by
  let g : ℝ → ℝ := signedTimeCutoff R epsilon t
  have hg : MapsTo g J (Icc (-r) r) := by
    intro z _
    have hz := signedTimeCutoff_mem hR hepsilon t z
    exact ⟨(neg_le_neg hepsr).trans hz.1, hz.2.trans hepsr⟩
  have hginj := injOn_transverse_cutoff F B (Icc (-r) r) J
    ((0 : E), (1 : ℝ)) g hF (L := L) (k := epsilon / R) hL htrans hg
    (fun z _ w _ => signedTimeCutoff_abs_sub_le hR hepsilon t z w) hsmall
  intro x hx y hy hxy
  apply hj hx hy
  apply hginj (hjmap hx) (hjmap hy)
  have hsource (x : E) (hx : x ∈ N) :
      ((j x).1, (g (j x).2, (j x).2)) ∈ B ×ˢ (Icc (-r) r ×ˢ J) :=
    ⟨(hjmap hx).1, hg (hjmap hx).2, (hjmap hx).2⟩
  apply Prod.ext
  · change (F ((j x).1, (g (j x).2, (j x).2))).1 - g (j x).2 • (0 : E) =
      (F ((j y).1, (g (j y).2, (j y).2))).1 - g (j y).2 • (0 : E)
    simpa only [jointProjectedCutoff, g, smul_zero, sub_zero] using hxy
  · change (F ((j x).1, (g (j x).2, (j x).2))).2 - g (j x).2 * 1 =
      (F ((j y).1, (g (j y).2, (j y).2))).2 - g (j y).2 * 1
    rw [hheight _ (hsource x hx), hheight _ (hsource y hy)]
    simp only [mul_one, sub_self]

end PoincareConjecture.M76.ZeroChargeJoint
