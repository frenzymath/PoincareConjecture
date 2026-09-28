import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualOrientation
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Poincare.Geometry.Manifold Poincare.Geometry.Manifold.RegularLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem planar_circle_embedding
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

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}




theorem exists_actual_lower_slice_circle_pair
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hunique : ∀ q ∈ P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) q = 0 → q = p)
    (hcount : Nat.card d.ends.LowerCutIndex = 2)
    {z : Real} (hz : z ∈ Ico d.ends.lowerCut (inner Real (M.v : E3) (g p))) :
    ∃ C : Fin 2 → S1 → E2,
      (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
      Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
      (⋃ i, range (C i)) = d.A z := by
  classical
  let h : S2 → Real := fun q => inner Real (M.v : E3) (g q)
  have hge := M.tree.embedding_of_mem_leaves hg
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp hge.contMDiff
  have hregular (q : S2) (hq : h q ∈ Icc d.ends.lowerCut z) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := by
    intro hc
    have hqcore : q ∈ P.core := d.ends.physical_middle_band_subset_core
      ⟨hq.1, by
        rw [d.upperCut_eq]
        change h q ≤ h p + d.eta
        linarith [hq.2, hz.2, d.eta_pos]⟩
    have hqp := hunique q hqcore hc
    subst q
    exact hz.2.not_ge hq.2
  obtain ⟨U, _, _, _, hfull, hreg, V, δ, Φ, _, _, _, _, _, _, _, hlevels⟩ :=
    exists_sphere_height_level_diffeomorphisms_on_regular_band_of_smooth hh hz.1 hregular
  let := openLevelSetChartedSpace hh U hreg 1 d.ends.lowerCut
  let := openLevelSetChartedSpace hh U hreg 1 z
  obtain ⟨T, _⟩ := hlevels z ⟨hz.1, le_rfl⟩
  let E : Fin 2 ≃ d.ends.LowerCutIndex :=
    (Fintype.equivFinOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using hcount)).symm
  let a (i : Fin 2) (q : S1) : openLevelSet h U d.ends.lowerCut :=
    ⟨⟨d.ends.lowerCutCircle (E i) q,
      (inter_eq_right.mp (hfull _ ⟨le_rfl, hz.1⟩)) (d.ends.lowerCutCircle_height (E i) q)⟩,
      d.ends.lowerCutCircle_height (E i) q⟩
  have ha (i : Fin 2) : ContMDiff (𝓡 1) (𝓡 1) ∞ (a i) := by
    intro q
    apply (contMDiffAt_into_openLevelSet_iff hh 1 _ U hreg (a i) q).mpr
    exact (d.ends.lowerCutCircle_geometry (E i)).1 q
  have had (i : Fin 2) (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 1) (a i) q) := by
    have hd := (d.ends.lowerCutCircle_geometry (E i)).2.2 q
    change Injective (mfderiv (𝓡 1) (𝓡 2)
      (openLevelIncl h U d.ends.lowerCut ∘ a i) q) at hd
    rw [mfderiv_comp q ((contMDiff_openLevelIncl hh U hreg 1 _ _).mdifferentiableAt
      (by simp)) (((ha i) q).mdifferentiableAt (by simp))] at hd
    intro u v huv
    apply hd
    exact congrArg (mfderiv (𝓡 1) (𝓡 2) (openLevelIncl h U d.ends.lowerCut) (a i q)) huv
  let s (i : Fin 2) : S1 → S2 := openLevelIncl h U z ∘ T ∘ a i
  have hs (i : Fin 2) : ContMDiff (𝓡 1) (𝓡 2) ∞ (s i) :=
    (contMDiff_openLevelIncl hh U hreg 1 z).comp (T.contMDiff.comp (ha i))
  have hsd (i : Fin 2) (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 2) (s i) q) := by
    dsimp [s]
    rw [mfderiv_comp q ((contMDiff_openLevelIncl hh U hreg 1 z _).mdifferentiableAt
      (by simp)) (((T.contMDiff.comp (ha i)) q).mdifferentiableAt (by simp)),
      mfderiv_comp q ((T.contMDiff _).mdifferentiableAt (by simp))
        (((ha i) q).mdifferentiableAt (by simp))]
    exact (injective_mfderiv_openLevelIncl hh U hreg 1 z _).comp
      ((T.mfderivToContinuousLinearEquiv (by simp) _).injective.comp (had i q))
  have hsi : Injective (fun x : Fin 2 × S1 => s x.1 x.2) := by
    rintro ⟨i, q⟩ ⟨j, r⟩ heq
    have hT : T (a i q) = T (a j r) := Subtype.ext (Subtype.ext heq)
    have hc := congrArg (openLevelIncl h U d.ends.lowerCut) (T.injective hT)
    have hpair := d.ends.lowerCutCircle_joint_injective (a₁ := (E i, q)) (a₂ := (E j, r)) hc
    exact Prod.ext (E.injective (congrArg Prod.fst hpair))
      (congrArg (fun x : d.ends.LowerCutIndex × S1 => x.2) hpair)
  have hheight (i : Fin 2) (q : S1) : h (s i q) = z := (T (a i q)).property
  have hcover : (⋃ i, range (s i)) = {q : S2 | h q = z} := by
    ext q
    constructor
    · intro hq
      obtain ⟨i, r, rfl⟩ := by simpa only [mem_iUnion, mem_range] using hq
      exact hheight i r
    · intro hq
      let qz : openLevelSet h U z :=
        ⟨⟨q, (inter_eq_right.mp (hfull z ⟨hz.1, le_rfl⟩)) hq⟩, hq⟩
      have hlow := (T.symm qz).property
      have hmem : openLevelIncl h U d.ends.lowerCut (T.symm qz) ∈
          ⋃ i, range (d.ends.lowerCutCircle i) := by
        rw [d.ends.iUnion_range_lowerCutCircle]
        exact hlow
      obtain ⟨j, r, hr⟩ := by simpa only [mem_iUnion, mem_range] using hmem
      refine mem_iUnion.mpr ⟨E.symm j, r, ?_⟩
      have heq : a (E.symm j) r = T.symm qz := by
        apply Subtype.ext
        apply Subtype.ext
        simpa only [a, E.apply_symm_apply, openLevelIncl] using hr
      change openLevelIncl h U z (T (a (E.symm j) r)) = q
      rw [heq, T.apply_symm_apply]
      rfl
  let k (i : Fin 2) : S1 → E3 := d.flatten ∘ g ∘ s i
  let C (i : Fin 2) : S1 → E2 := Saddle.toE2 ∘ k i
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
    ((d.frame_height (d.D (g (s i q)))).trans (d.D_height _)).trans (hheight i q)
  have hcoord (i : Fin 2) (q : S1) : Saddle.toE3 (C i q) z = k i q := by
    ext j
    fin_cases j <;> simp [C, Saddle.toE2, Saddle.toE3, hkheight, Function.comp_def]
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i
    apply planar_circle_embedding (k i) (hk i) _ (hkd i) z (hkheight i)
    exact d.flatten.injective.comp (hge.isEmbedding.injective.comp
      (fun q r hqr => congrArg Prod.snd (hsi (a₁ := (i,q)) (a₂ := (i,r)) hqr)))
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
      have hq : h q = z := by
        have hc := congrArg (fun y : E3 => y 2) hqx
        rw [show d.flatten (g q) 2 = h q from
          (d.frame_height (d.D (g q))).trans (d.D_height _)] at hc
        exact hc
      have hmem : q ∈ ⋃ i, range (s i) := hcover.symm ▸ hq
      obtain ⟨i, r, hr⟩ := by simpa only [mem_iUnion, mem_range] using hmem
      refine mem_iUnion.mpr ⟨i, r, ?_⟩
      change Saddle.toE2 (d.flatten (g (s i r))) = x
      rw [hr, hqx]
      ext j
      fin_cases j <;> rfl

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
