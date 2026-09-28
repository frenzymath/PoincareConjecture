import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualCircles
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.Resolution







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel _root_.Poincare.Geometry.Manifold SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem planar_embedding_of_constant_height
    (k : S1 → E3) (hk : ContMDiff (𝓡 1) (𝓡 3) ∞ k)
    (hki : Injective k) (hkd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 3) k q))
    (z : Real) (hz : ∀ q, k q 2 = z) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (Saddle.toE2 ∘ k) := by
  have hp : ContMDiff (𝓡 3) (𝓡 2) ∞ Saddle.toE2 := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
  have hl : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun x => Saddle.toE3 x z) := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
    · exact contDiff_const
  have heq : (fun x => Saddle.toE3 x z) ∘ (Saddle.toE2 ∘ k) = k := by
    funext q
    ext i
    fin_cases i <;> simp [Saddle.toE2, Saddle.toE3, hz, Function.comp_def]
  apply isSmoothEmbedding_of_injective_mfderiv (hp.comp hk)
  · intro q r hqr
    apply hki
    rw [← heq]
    exact congrArg (fun x => Saddle.toE3 x z) hqr
  · intro q
    have hd := hkd q
    rw [← heq, mfderiv_comp q ((hl _).mdifferentiableAt (by simp))
      (((hp.comp hk) q).mdifferentiableAt (by simp))] at hd
    intro u v huv
    apply hd
    exact congrArg (mfderiv (𝓡 2) (𝓡 3) (fun x => Saddle.toE3 x z)
      ((Saddle.toE2 ∘ k) q)) huv

private theorem circle_pair_not_preconnected
    (C : Fin 2 → S1 → E2) (hC : ∀ i, Continuous (C i))
    (hinj : Injective (fun x : Fin 2 × S1 => C x.1 x.2)) :
    ¬ IsPreconnected (⋃ i, range (C i)) := by
  intro hc
  have hdis : Disjoint (range (C 0)) (range (C 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨q, hq⟩ ⟨r, hr⟩
    have hi := congrArg Prod.fst (hinj (a₁ := (0,q)) (a₂ := (1,r)) (hq.trans hr.symm))
    exact (by decide : (0 : Fin 2) ≠ 1) hi
  have hcover : (⋃ i, range (C i)) ⊆ range (C 0) ∪ range (C 1) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  have hs := isPreconnected_iff_subset_of_disjoint_closed.mp hc
    (range (C 0)) (range (C 1)) (isCompact_range (hC 0)).isClosed
    (isCompact_range (hC 1)).isClosed hcover (by rw [hdis.inter_eq, inter_empty])
  let q : S1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  rcases hs with hs | hs
  · exact disjoint_left.mp hdis (hs (mem_iUnion_of_mem 1 (mem_range_self q))) (mem_range_self q)
  · exact disjoint_left.mp hdis (mem_range_self q) (hs (mem_iUnion_of_mem 0 (mem_range_self q)))

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}




theorem exists_actual_negative_branch_circle_pairs
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (hcount : Nat.card d.ends.LowerCutIndex = 2) :
    ∃ r δ : Real, 0 < r ∧ closedSquare r ⊆ e.source ∧
      0 < δ ∧ δ < d.eta ∧ δ < r ^ 2 ∧
      ∀ t ∈ Ioc (0 : Real) δ,
        ∃ C : Fin 2 → S1 → E2,
          (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
          Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
          (⋃ i, range (C i)) = d.A (inner Real (M.v : E3) (g p) - t) ∧
          ∀ i s, s ∈ Icc (-hyperbolaRadius r t) (hyperbolaRadius r t) →
            Saddle.toE2 (d.flatten (g (e (negativeLevelArc t i s)))) ∈ range (C i) := by
  classical
  obtain ⟨r, δ, hr, _, hrs, hδ, hδη, hδr, hresolution⟩ :=
    M.exists_terminal_saddle_cut_resolution hg P hP hcaps hp hc e he0 hep he hei hform d.eta_pos
  refine ⟨r, δ, hr, hrs, hδ, hδη, hδr, ?_⟩
  intro t ht
  let z := inner Real (M.v : E3) (g p) - t
  have hz : z ∈ Ico d.ends.lowerCut (inner Real (M.v : E3) (g p)) := by
    rw [d.lowerCut_eq]
    dsimp [z]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨A, hlow, _, _, hcase⟩ := hresolution t ht.1 ht.2
  have hlabel : ∃ E : Fin 2 ≃ A.LowerCutIndex,
      ∀ i, negativePatchArc e r t i ⊆ range (A.lowerCutCircle (E i)) := by
    rcases hcase with ⟨hone, _⟩ | ⟨_, E, hE⟩
    · exfalso
      obtain ⟨C, hC, hinj, hcover⟩ := exists_actual_lower_slice_circle_pair hg d hunique hcount hz
      have hnot : ¬ IsPreconnected (d.A z) := by
        rw [← hcover]
        exact circle_pair_not_preconnected C (fun i => (hC i).contMDiff.continuous) hinj
      apply hnot
      apply (actual_slice_preconnected_iff hg d z).mpr
      obtain ⟨i, hi⟩ := Nat.card_eq_one_iff_exists.mp hone
      have hlevel : {q : S2 | inner Real (M.v : E3) (g q) = z} =
          range (A.lowerCutCircle i) := by
        dsimp [z]
        rw [← hlow, ← A.iUnion_range_lowerCutCircle]
        ext q
        simp only [mem_iUnion]
        constructor
        · rintro ⟨j, hj⟩
          rwa [hi j] at hj
        · intro hq
          exact ⟨i, hq⟩
      rw [hlevel]
      exact isPreconnected_range (A.lowerCutCircle_geometry i).1.continuous
    · exact ⟨E, hE⟩
  obtain ⟨E, hE⟩ := hlabel
  let s (i : Fin 2) := A.lowerCutCircle (E i)
  have hs (i : Fin 2) := (A.lowerCutCircle_geometry (E i)).1
  have hsd (i : Fin 2) := (A.lowerCutCircle_geometry (E i)).2.2
  have hsi : Injective (fun x : Fin 2 × S1 => s x.1 x.2) := by
    rintro ⟨i, q⟩ ⟨j, v⟩ heq
    have hpq := A.lowerCutCircle_joint_injective (a₁ := (E i,q)) (a₂ := (E j,v)) heq
    exact Prod.ext (E.injective (congrArg Prod.fst hpq))
      (congrArg (fun x : A.LowerCutIndex × S1 => x.2) hpq)
  let k (i : Fin 2) : S1 → E3 := d.flatten ∘ g ∘ s i
  let C (i : Fin 2) : S1 → E2 := Saddle.toE2 ∘ k i
  have hge := M.tree.embedding_of_mem_leaves hg
  have hk (i : Fin 2) : ContMDiff (𝓡 1) (𝓡 3) ∞ (k i) :=
    d.flatten.contMDiff.comp (hge.contMDiff.comp (hs i))
  have hkd (i : Fin 2) (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) (k i) q) := by
    dsimp [k]
    rw [mfderiv_comp q ((d.flatten.contMDiff _).mdifferentiableAt (by simp))
      (((hge.contMDiff.comp (hs i)) q).mdifferentiableAt (by simp)),
      mfderiv_comp q ((hge.contMDiff _).mdifferentiableAt (by simp))
        (((hs i) q).mdifferentiableAt (by simp))]
    exact (d.flatten.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      ((injective_mfderiv_sphere_embedding hge _).comp (hsd i q))
  have hkheight (i : Fin 2) (q : S1) : k i q 2 = z :=
    ((d.frame_height (d.D (g (s i q)))).trans (d.D_height _)).trans
      ((A.lowerCutCircle_height (E i) q).trans hlow)
  have hcoord (i : Fin 2) (q : S1) : Saddle.toE3 (C i q) z = k i q := by
    ext j
    fin_cases j <;> simp [C, Saddle.toE2, Saddle.toE3, hkheight, Function.comp_def]
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · intro i
    exact planar_embedding_of_constant_height (k i) (hk i)
      (d.flatten.injective.comp (hge.isEmbedding.injective.comp
        (A.lowerCutCircle_geometry (E i)).2.1)) (hkd i) z (hkheight i)
  · intro x y hxy
    apply hsi
    apply hge.isEmbedding.injective
    apply d.flatten.injective
    exact (hcoord x.1 x.2).symm.trans ((congrArg (fun x => Saddle.toE3 x z) hxy).trans
      (hcoord y.1 y.2))
  · ext x
    constructor
    · intro hx
      obtain ⟨i, q, rfl⟩ := by simpa only [mem_iUnion, mem_range] using hx
      change Saddle.toE3 (C i q) z ∈ d.flatten '' range g
      rw [hcoord]
      exact mem_image_of_mem _ (mem_range_self (s i q))
    · rintro ⟨_, ⟨q, rfl⟩, hqx⟩
      have hq : inner Real (M.v : E3) (g q) = A.lowerCut := by
        rw [hlow]
        have hcq := congrArg (fun y : E3 => y 2) hqx
        rw [show d.flatten (g q) 2 = inner Real (M.v : E3) (g q) from
          (d.frame_height (d.D (g q))).trans (d.D_height _)] at hcq
        exact hcq
      have hmem : q ∈ ⋃ i, range (A.lowerCutCircle i) := A.iUnion_range_lowerCutCircle.symm ▸ hq
      obtain ⟨j, v, hv⟩ := by simpa only [mem_iUnion, mem_range] using hmem
      refine mem_iUnion.mpr ⟨E.symm j, v, ?_⟩
      change Saddle.toE2 (d.flatten (g (A.lowerCutCircle (E (E.symm j)) v))) = x
      rw [E.apply_symm_apply, hv, hqx]
      ext i
      fin_cases i <;> rfl
  · intro i u hu
    obtain ⟨q, hq⟩ := hE i (mem_image_of_mem e (mem_image_of_mem _ hu))
    refine ⟨q, ?_⟩
    exact congrArg (fun q => Saddle.toE2 (d.flatten (g q))) hq

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
