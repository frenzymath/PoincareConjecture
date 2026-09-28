import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M25.Mathlib.TwoEndedFiberwiseInterpolation
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ThreePieceCollars
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.OpenPartialHomeomorph.Composition










set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture.M25



theorem exists_compatible_product_clocks
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {eta : ℝ} (heta : 0 < eta)
    (e : Fin 3 → OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : ∀ i : Fin 3,
      (e i).source = univ ×ˢ Ioo (-eta) (1 + eta))
    (hsmooth : ∀ i : Fin 3,
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (e i) (e i).source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (e i).symm (e i).target)
    (hboundary : ∀ i : Fin 3,
      range (fun q : UnitTwoSphere => e i (q, 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)))
    (hinter : ∀ i : Fin 3,
      (e i '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
          (e (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)))
    (hcover : (⋃ i : Fin 3, e i '' (univ ×ˢ Icc (0 : ℝ) 1)) = univ) :
    let K : Fin 3 → Set M := fun i => e i '' (univ ×ˢ Icc (0 : ℝ) 1)
    ∃ (D : Fin 3 → Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞)
      (delta : ℝ),
      0 < delta ∧ delta < eta ∧ delta < 1 / 8 ∧
      (∀ (i : Fin 3) (z : RoundCylinderSpace),
        (D i z).1 = z.1 ∧ ((D i).symm z).1 = z.1) ∧
      (∀ (i : Fin 3) (q : UnitTwoSphere),
        D i (q, 0) = (q, 0) ∧ D i (q, 1) = (q, 1)) ∧
      (∀ (i : Fin 3) (q : UnitTwoSphere) (s : ℝ),
        0 < deriv (fun t : ℝ => (D i (q, t)).2) s) ∧
      (∀ i : Fin 3,
        D i '' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
        D i ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc (0 : ℝ) 1 ∧
        D i '' (univ ×ˢ Ioo (0 : ℝ) 1) = univ ×ˢ Ioo (0 : ℝ) 1 ∧
        D i ⁻¹' (univ ×ˢ Ioo (0 : ℝ) 1) = univ ×ˢ Ioo (0 : ℝ) 1) ∧
      (∀ (i : Fin 3) (q : UnitTwoSphere) (s : ℝ),
        s ∈ Ioo (-delta) delta →
          e i (q, s) ∈ (e (i - 1)).target ∧
          (e i (q, s) ∈ K i ↔ 0 ≤ s) ∧
          (e i (q, s) ∈ K (i - 1) ↔ s ≤ 0) ∧
          e i (q, s) ∉ K (i + 1) ∧
          (D i (q, s)).2 = s ∧
          (D (i - 1) ((e (i - 1)).symm (e i (q, s)))).2 = 1 + s) := by
  classical
  dsimp only
  obtain ⟨r, hr, hreta, _hreighth, hlower, hupper⟩ :=
    exists_signed_collars_of_three_product_charts heta e hsource hsmooth hboundary
      hinter hcover
  have hlowSource (i : Fin 3) : univ ×ˢ Ioo (-r) r ⊆ (e i).source := by
    intro z hz
    rw [hsource i]
    exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have huppSource (i : Fin 3) : univ ×ˢ Ioo (1 - r) (1 + r) ⊆ (e i).source := by
    intro z hz
    rw [hsource i]
    exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hzeroSource (i : Fin 3) (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ (e i).source := by
    rw [hsource i]
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have honeSource (i : Fin 3) (q : UnitTwoSphere) : (q, (1 : ℝ)) ∈ (e i).source := by
    rw [hsource i]
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  let g1 : Fin 3 → RoundCylinderSpace → ℝ := fun i z =>
    1 + ((e (i + 1)).symm (e i z)).2
  have hg1 (i : Fin 3) :
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (g1 i)
        (univ ×ˢ Ioo (1 - r) (1 + r)) := by
    have htrans := (hsmooth (i + 1)).2.comp ((hsmooth i).1.mono (huppSource i))
      (fun z hz => (hupper i z.1 z.2 hz.2).1)
    exact contMDiff_const.contMDiffOn.add (contMDiff_snd.comp_contMDiffOn htrans)
  have hg1one (i : Fin 3) (q : UnitTwoSphere) : g1 i (q, 1) = 1 := by
    have hx : e i (q, 1) ∈ range (fun p : UnitTwoSphere => e (i + 1) (p, 0)) := by
      rw [← hboundary i]
      exact ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := hx
    dsimp only [g1]
    rw [← hp, (e (i + 1)).left_inv (hzeroSource (i + 1) p)]
    simp
  have hd1 (i : Fin 3) (q : UnitTwoSphere) (s : ℝ)
      (hs : s ∈ Ioo (1 - r) (1 + r)) :
      0 < deriv (fun t : ℝ => g1 i (q, t)) s := by
    simpa only [g1, deriv_const_add] using (hupper i q s hs).2
  have hext (i : Fin 3) :=
    Diffeomorph.exists_two_ended_fiberwise_interpolation
      (I := 𝓡 2) (K := UnitTwoSphere) Prod.snd (g1 i) hr
      contMDiff_snd.contMDiffOn (hg1 i) (fun _ => rfl) (hg1one i)
      (by intro q s _; simp) (hd1 i)
  choose rho D hrho _hror _hrhoEighth hangular hfixed hderiv hlow hhigh
    hclosedImage hclosedPre hopenImage hopenPre using hext
  let tau : Fin 3 → RoundCylinderSpace → ℝ := fun i z =>
    ((e (i - 1)).symm (e i z)).2
  have htau (i : Fin 3) : ContinuousOn (tau i) (univ ×ˢ Ioo (-r) r) := by
    exact ((e (i - 1)).symm.continuousOn.comp
      ((e i).continuousOn.mono (hlowSource i))
      (fun z hz => (hlower i z.1 z.2 hz.2).1)).snd
  have htauZero (i : Fin 3) (q : UnitTwoSphere) : tau i (q, 0) = 1 := by
    have hb := hboundary (i - 1)
    rw [sub_add_cancel] at hb
    have hx : e i (q, 0) ∈ range (fun p : UnitTwoSphere => e (i - 1) (p, 1)) := by
      rw [hb]
      exact ⟨q, rfl⟩
    obtain ⟨p, hp⟩ := hx
    dsimp only [tau]
    rw [← hp, (e (i - 1)).left_inv (honeSource (i - 1) p)]
  let O : Fin 3 → Set RoundCylinderSpace := fun i =>
    (univ ×ˢ Ioo (-r) r) ∩ tau i ⁻¹' Ioo (1 - rho (i - 1)) (1 + rho (i - 1))
  have hO (i : Fin 3) : IsOpen (O i) :=
    (htau i).isOpen_inter_preimage (isOpen_univ.prod isOpen_Ioo) isOpen_Ioo
  have hslice (i : Fin 3) : (univ : Set UnitTwoSphere) ×ˢ {(0 : ℝ)} ⊆ O i := by
    rintro ⟨q, s⟩ ⟨_, hs⟩
    have hs0 : s = 0 := mem_singleton_iff.mp hs
    subst s
    refine ⟨⟨mem_univ _, by constructor <;> linarith⟩, ?_⟩
    change 1 - rho (i - 1) < tau i (q, 0) ∧ tau i (q, 0) < 1 + rho (i - 1)
    rw [htauZero i q]
    constructor <;> linarith [hrho (i - 1)]
  have hband (i : Fin 3) : ∃ a : ℝ, 0 < a ∧ univ ×ˢ Ioo (-a) a ⊆ O i := by
    obtain ⟨U, V, _, hV, hU, hV0, hUV⟩ :=
      generalized_tube_lemma isCompact_univ isCompact_singleton (hO i) (hslice i)
    have h0V : (0 : ℝ) ∈ V := hV0 (mem_singleton 0)
    obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
    refine ⟨a, ha, ?_⟩
    intro z hz
    have hzV : z.2 ∈ V := hball (by simpa [Real.dist_eq] using abs_lt.mpr hz.2)
    exact hUV ⟨hU (mem_univ z.1), hzV⟩
  choose a ha hraw using hband
  let m : Fin 3 → ℝ := fun i => min (rho i) (a i)
  have hm (i : Fin 3) : 0 < m i := lt_min (hrho i) (ha i)
  have hmin : 0 < min r (min (1 / 8 : ℝ) (min (m 0) (min (m 1) (m 2)))) :=
    lt_min hr (lt_min (by norm_num) (lt_min (hm 0) (lt_min (hm 1) (hm 2))))
  obtain ⟨delta, hd, hsmall⟩ := exists_between hmin
  obtain ⟨hdr, hsmall⟩ := lt_min_iff.mp hsmall
  obtain ⟨hdeighth, hsmall⟩ := lt_min_iff.mp hsmall
  obtain ⟨hd0, hsmall⟩ := lt_min_iff.mp hsmall
  obtain ⟨hd1, hd2⟩ := lt_min_iff.mp hsmall
  have hdm (i : Fin 3) : delta < m i := by
    fin_cases i
    · exact hd0
    · exact hd1
    · exact hd2
  have hdrho (i : Fin 3) : delta < rho i := (hdm i).trans_le (min_le_left _ _)
  have hda (i : Fin 3) : delta < a i := (hdm i).trans_le (min_le_right _ _)
  refine ⟨D, delta, hd, hdr.trans hreta, hdeighth, hangular, hfixed, hderiv,
    (fun i => ⟨hclosedImage i, hclosedPre i, hopenImage i, hopenPre i⟩), ?_⟩
  intro i q s hs
  have hsr : s ∈ Ioo (-r) r := by constructor <;> linarith [hs.1, hs.2]
  obtain ⟨htarget, hcurrent, hprevious, havoid⟩ := hlower i q s hsr
  refine ⟨htarget, hcurrent, hprevious, havoid, ?_, ?_⟩
  · exact hlow i ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2, hdrho i]⟩
  · have hsa : s ∈ Ioo (-(a i)) (a i) := by
      constructor <;> linarith [hs.1, hs.2, hda i]
    have hlanding : ((e (i - 1)).symm (e i (q, s))).2 ∈
        Ioo (1 - rho (i - 1)) (1 + rho (i - 1)) :=
      (hraw i (show (q, s) ∈ univ ×ˢ Ioo (-(a i)) (a i) from ⟨mem_univ q, hsa⟩)).2
    have hvalue : (D (i - 1) ((e (i - 1)).symm (e i (q, s)))).2 =
        g1 (i - 1) ((e (i - 1)).symm (e i (q, s))) :=
      hhigh (i - 1) ⟨mem_univ _, hlanding⟩
    have hssource : (q, s) ∈ (e i).source := hlowSource i ⟨mem_univ q, hsr⟩
    rw [hvalue]
    simp only [g1, sub_add_cancel, (e (i - 1)).right_inv htarget,
      (e i).left_inv hssource]

end PoincareConjecture.M25
