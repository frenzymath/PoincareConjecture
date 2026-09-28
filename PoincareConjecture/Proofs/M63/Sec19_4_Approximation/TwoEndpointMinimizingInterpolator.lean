import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.LocalSmoothMinimizingInterpolator
import PoincareConjecture.Proofs.M58.Sec18_4_UniformRadius











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M63




theorem exists_smooth_minimizing_interpolator
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M)
    (hcompact : IsCompact (univ : Set M)) :
    ∃ r : ℝ, 0 < r ∧
      ∃ H : ℝ × (M × M) → M,
        ContMDiffOn
          ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
          (Ioo (-1 : ℝ) 2 ×ˢ
            {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}) ∧
        (∀ p q, g.edist p q < ENNReal.ofReal r →
          H (0, p, q) = p ∧ H (1, p, q) = q ∧
          g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
          (∀ t ∈ Ioo (-1 : ℝ) 2,
            g.tangentNorm (H (t, p, q))
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, p, q)) t 1) =
                (g.edist p q).toReal) ∧
          g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q ∧
          (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            g.edist (H (s, p, q)) (H (t, p, q)) =
              ENNReal.ofReal |s - t| * g.edist p q)) ∧
        (∀ p t, H (t, p, p) = p) ∧
        (∀ p q, g.edist p q < ENNReal.ofReal r →
          ∀ gamma : ℝ → M,
            g.IsGeodesicOn gamma (Ioo (-1 : ℝ) 2) →
            gamma 0 = p → gamma 1 = q →
            g.pathELength gamma 0 1 = g.edist p q →
            EqOn gamma (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2)) := by
  classical
  choose O hOopen hOcenter Hloc hSmooth hProperties hDiagonal hUnique using
    fun p0 : M => exists_local_smooth_minimizing_interpolator g hcompact p0
  let U : Set (M × M) := ⋃ p0 : M, O p0 ×ˢ O p0
  have hUopen : IsOpen U := isOpen_iUnion (fun p0 => (hOopen p0).prod (hOopen p0))
  have hUdiag (p : M) : (p, p) ∈ U := mem_iUnion.mpr ⟨p, hOcenter p, hOcenter p⟩
  let pick : U → M := fun pq => (mem_iUnion.mp pq.property).choose
  have hpick (pq : U) : pq.1 ∈ O (pick pq) ×ˢ O (pick pq) :=
    (mem_iUnion.mp pq.property).choose_spec
  let H : ℝ × (M × M) → M := fun w =>
    if w.2.1 = w.2.2 then w.2.1
    else if hw : w.2 ∈ U then Hloc (pick ⟨w.2, hw⟩) w else w.2.1
  have hdiag (p : M) (t : ℝ) : H (t, p, p) = p := by simp only [H, if_true]

  have hlocalEq (p0 : M) :
      EqOn H (Hloc p0) (Ioo (-1 : ℝ) 2 ×ˢ (O p0 ×ˢ O p0)) := by
    rintro ⟨t, p, q⟩ ⟨ht, hp, hq⟩
    by_cases hpq : p = q
    · subst q
      exact (hdiag p t).trans (hDiagonal p0 p hp t ht).symm
    have hU : (p, q) ∈ U := mem_iUnion.mpr ⟨p0, hp, hq⟩
    change (if p = q then p else
      if hw : (p, q) ∈ U then Hloc (pick ⟨(p, q), hw⟩) (t, p, q) else p) = _
    rw [if_neg hpq, dif_pos hU]
    have hpicked := hpick ⟨(p, q), hU⟩
    obtain ⟨_, h0, h1, hgeo, _, hlength, _⟩ :=
      hProperties (pick ⟨(p, q), hU⟩) p hpicked.1 q hpicked.2
    exact hUnique p0 p hp q hq (fun s => Hloc (pick ⟨(p, q), hU⟩) (s, p, q))
      hgeo h0 h1 hlength ht
  have hglobalSmooth : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U) := by
    intro w hw
    obtain ⟨p0, hpq⟩ := mem_iUnion.mp hw.2
    have hopen : IsOpen (Ioo (-1 : ℝ) 2 ×ˢ (O p0 ×ˢ O p0)) :=
      isOpen_Ioo.prod ((hOopen p0).prod (hOopen p0))
    have hmem : w ∈ Ioo (-1 : ℝ) 2 ×ˢ (O p0 ×ˢ O p0) := ⟨hw.1, hpq⟩
    have heq : H =ᶠ[𝓝 w] Hloc p0 := by
      filter_upwards [hopen.mem_nhds hmem] with v hv
      exact hlocalEq p0 hv
    exact (((hSmooth p0).contMDiffAt (hopen.mem_nhds hmem)).congr_of_eventuallyEq
      heq).contMDiffWithinAt
  have hgerm (p0 : M) {p q : M} (hp : p ∈ O p0) (hq : q ∈ O p0)
      {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 2) :
      (fun s => H (s, p, q)) =ᶠ[𝓝 t] fun s => Hloc p0 (s, p, q) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hlocalEq p0 ⟨hs, hp, hq⟩
  have hclosed : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hproperties (p q : M) (hpq : (p, q) ∈ U) :
      H (0, p, q) = p ∧ H (1, p, q) = q ∧
      g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal) ∧
      g.pathELength (fun t => H (t, p, q)) 0 1 = g.edist p q ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        g.edist (H (s, p, q)) (H (t, p, q)) =
          ENNReal.ofReal |s - t| * g.edist p q) := by
    obtain ⟨p0, hp, hq⟩ := mem_iUnion.mp hpq
    obtain ⟨hdist, h0, h1, hgeo, hspeed, _hlength, hsegment⟩ := hProperties p0 p hp q hq
    have hnewGeo : g.IsGeodesicOn (fun t => H (t, p, q)) (Ioo (-1 : ℝ) 2) := by
      intro t ht
      obtain ⟨r, y, v, hcoords⟩ := hgeo t ht
      refine ⟨r, y, v, ?_⟩
      filter_upwards [hcoords, hgerm p0 hp hq ht] with s hs heq
      exact ⟨heq.trans hs.1, hs.2⟩
    have hnewSpeed : ∀ t ∈ Ioo (-1 : ℝ) 2,
        g.tangentNorm (H (t, p, q))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s => H (s, p, q)) t 1) =
            (g.edist p q).toReal := by
      intro t ht
      have hbase : H (t, p, q) = Hloc p0 (t, p, q) :=
        (hgerm p0 hp hq ht).self_of_nhds
      rw [(hgerm p0 hp hq ht).mfderiv_eq, hbase]
      exact hspeed t ht
    have hfinite : g.edist p q ≠ ⊤ := ne_top_of_lt (hdist.trans_le le_top)
    refine ⟨(hlocalEq p0 ⟨by norm_num, hp, hq⟩).trans h0,
      (hlocalEq p0 ⟨by norm_num, hp, hq⟩).trans h1, hnewGeo, hnewSpeed, ?_, ?_⟩
    · have hh := g.pathELength_eq_of_tangentNorm_eq (a := 0) (b := 1)
        (fun t ht => hnewSpeed t (hclosed ht))
      simpa only [sub_zero, ENNReal.ofReal_one, mul_one,
        ENNReal.ofReal_toReal hfinite] using hh
    · intro s hs t ht
      rw [hlocalEq p0 ⟨hclosed hs, hp, hq⟩, hlocalEq p0 ⟨hclosed ht, hp, hq⟩]
      exact hsegment s hs t ht
  obtain ⟨r, hr, hrU⟩ :=
    Proofs.M58.exists_uniform_riemannian_radius g hcompact hUopen hUdiag
  refine ⟨r, hr, H, hglobalSmooth.mono (Set.prod_mono Subset.rfl ?_),
    (fun p q hpq => hproperties p q (hrU p q hpq)), hdiag, ?_⟩
  · exact fun pq hpq => hrU pq.1 pq.2 hpq
  · intro p q hpq gamma hgamma h0 h1 hlength
    obtain ⟨p0, hp, hq⟩ := mem_iUnion.mp (hrU p q hpq)
    have heq := hUnique p0 p hp q hq gamma hgamma h0 h1 hlength
    intro t ht
    exact (heq ht).trans (hlocalEq p0 ⟨ht, hp, hq⟩).symm

end PoincareConjecture.M63
