import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleLowerLevelCount
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleSourceCutMatching
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleTwoLevelTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.SaddleTransportedPieces

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_two_circle_side
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), psi (p, 0)⟫_ℝ
    let c : ℝ := f D.point
    ∃ delta : ℝ, 0 < delta ∧ delta < epsilon ∧
      ((∃ q : Fin 2 → UnitCircle → UnitTwoSphere,
        (∀ i : Fin 2,
          ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
          ∀ theta : UnitCircle,
            Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta)) ∧
        (∀ i k : Fin 2, i ≠ k → Disjoint (range (q i)) (range (q k))) ∧
        (⋃ i : Fin 2, range (q i)) = {p | f p = c - delta}) ∨
       (∃ q : Fin 2 → UnitCircle → UnitTwoSphere,
        (∀ i : Fin 2,
          ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
          ∀ theta : UnitCircle,
            Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta)) ∧
        (∀ i k : Fin 2, i ≠ k → Disjoint (range (q i)) (range (q k))) ∧
        (⋃ i : Fin 2, range (q i)) = {p | f p = c + delta})) := by
  classical
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  let f : UnitTwoSphere → ℝ := fun p => ⟪(u : E3), j p⟫_ℝ
  let c := f D.point
  obtain ⟨R, delta, N, hR, hd, hdE, hdR, hmorse, hcore, hN, _hreg,
    n, q, hn, hq, hdis, hlevel⟩ :=
    exists_saddle_lower_level_count psi hpsi u D epsilon hepsilon
  refine ⟨delta, hd, hdE, ?_⟩
  rcases hn with hn | hn
  · subst n
    let r := 5 * R / 8
    let Dc := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ r ^ 2}
    let Do := D.morse.symm '' {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 < r ^ 2}
    let aa := Real.sqrt ((r ^ 2 - delta) / 2)
    let bb := Real.sqrt ((r ^ 2 + delta) / 2)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let pm : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (sx i * aa, sy i * bb))
    let pp : Fin 4 → UnitTwoSphere := fun i => D.morse.symm (N (sx i * bb, sy i * aa))
    let Lm := range j ∩ {y | ⟪(u : E3), y⟫_ℝ = c - delta}
    let Lp := range j ∩ {y | ⟪(u : E3), y⟫_ℝ = c + delta}
    let C := j '' Dc
    let O := j '' Do
    have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
    have hji : Injective j := by
      intro p z hpz
      exact congrArg Prod.fst (hpsi.2.1
        ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpz)
    have himage (z : ℝ) : j '' {p | f p = z} =
        range j ∩ {y | ⟪(u : E3), y⟫_ℝ = z} := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨mem_range_self p, hp⟩
      · rintro ⟨⟨p, rfl⟩, hp⟩
        exact ⟨p, hp, rfl⟩
    have hDoDc : Do ⊆ Dc := image_mono (fun s hs =>
      (show s.1 ^ 2 + s.2 ^ 2 < r ^ 2 from hs).le)
    have hOC : O ⊆ C := image_mono hDoDc
    obtain ⟨_gm, gp, hgp, _hgmDis, hgpDis, hends, _hminusDisc,
      _hminusOpen, hplusDisc⟩ :=
      saddle_source_disc_arc_geometry psi u D R delta N hR hd hdR hmorse hN
    obtain ⟨alpha, ends, label, ha, haDis, hminusCover, hinc, hmatch⟩ :=
      exists_saddle_one_circle_exterior_matching psi hpsi u D R delta N
        hR hd hdR hmorse hcore hN q hq hlevel
    obtain ⟨F, hport, hpm, hwall, hflow⟩ :=
      exists_saddle_two_level_transport psi hpsi u D R delta N
        hR hd hdR hmorse hcore hN
    let a : Fin 2 → ℝ → E3 := fun i t => j (alpha i t)
    let g : Fin 2 → unitInterval → E3 := fun i t => j (gp i t)
    have haAmbient (i : Fin 2) : Continuous (a i) := hj.comp (ha i)
    have hgAmbient (i : Fin 2) : Continuous (g i) := hj.comp (hgp i).2.2.1
    have haDisAmbient : Disjoint (a 0 '' Icc (0 : ℝ) 1) (a 1 '' Icc (0 : ℝ) 1) := by
      apply disjoint_left.mpr
      rintro x ⟨s, hs, rfl⟩ ⟨t, ht, hts⟩
      exact disjoint_left.mp haDis ⟨s, hs, rfl⟩ ⟨t, ht, hji hts⟩
    have hgDisAmbient : Disjoint (range (g 0)) (range (g 1)) := by
      apply disjoint_left.mpr
      rintro x ⟨s, rfl⟩ ⟨t, hts⟩
      exact disjoint_left.mp hgpDis ⟨s, rfl⟩ ⟨t, hji hts⟩
    have hminusAmbient : Lm \ O = ⋃ i, a i '' Icc (0 : ℝ) 1 := by
      have hh := congrArg (fun s : Set UnitTwoSphere => j '' s) hminusCover
      rw [image_sdiff hji, himage, image_iUnion] at hh
      simp only [image_image] at hh
      simp only [O, Do, image_image, a]
      exact hh
    have hlocalAmbient : Lp ∩ C = ⋃ i, range (g i) := by
      have hh := congrArg (fun s : Set UnitTwoSphere => j '' s) hplusDisc
      rw [image_inter hji, himage, image_iUnion] at hh
      simp only [← range_comp] at hh
      exact hh
    have hincAmbient (i : Fin 2) : (a i '' Icc (0 : ℝ) 1) ∩ C =
        {j (pm (ends (i, 0))), j (pm (ends (i, 1)))} := by
      have hh := congrArg (fun s : Set UnitTwoSphere => j '' s) (hinc i)
      rw [image_inter hji, image_image, image_insert_eq, image_singleton] at hh
      exact hh
    have hendAmbient (i : Fin 2) :
        g i 0 = j (pp (finProdFinEquiv (i, (0 : Fin 2)))) ∧
        g i 1 = j (pp (finProdFinEquiv ((![1, 0] : Fin 2 → Fin 2) i, (1 : Fin 2)))) :=
      ⟨congrArg j (hends i).2.2.1, congrArg j (hends i).2.2.2⟩
    obtain ⟨K, hK, hKdis, hKcover⟩ := exists_saddle_transported_two_pieces
      F Lm Lp C O hOC (j ∘ pm) (j ∘ pp) ends label a g
      haAmbient hgAmbient haDisAmbient hgDisAmbient hminusAmbient hlocalAmbient
      hincAmbient hpm hport hwall hflow hendAmbient hmatch
    have hregPlus (p : UnitTwoSphere) (hp : f p = c + delta) :
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0 := by
      have hpcore : p ∈ D.sourceCore := hcore p (by
        change |f p - c| ≤ 3 * delta
        rw [hp, add_sub_cancel_left, abs_of_pos hd]
        linarith)
      intro hc
      have heq := (D.unique_critical p hpcore).mp hc
      subst p
      change c = c + delta at hp
      linarith
    obtain ⟨nPlus, qPlus, _components, hqPlus, hqPlusDis, hqPlusLevel, _hcomponents⟩ :=
      exists_regular_source_level_family psi hpsi (u : E3) (c + delta) hregPlus
    have hQcover : (⋃ i, range (fun theta => psi (qPlus i theta, 0))) = Lp := by
      have hh := congrArg (fun s : Set UnitTwoSphere => j '' s) hqPlusLevel
      rw [image_iUnion, himage] at hh
      simp only [← range_comp] at hh
      exact hh
    obtain ⟨q2, hq2, hq2Dis, hq2Level⟩ := exists_two_circles_of_ambient_partition
      psi hpsi nPlus qPlus hqPlus hqPlusDis K (fun i => (hK i).1)
      (fun i => (hK i).2) hKdis (hQcover.trans hKcover.symm)
    exact Or.inr ⟨q2, hq2, hq2Dis, hq2Level.trans hqPlusLevel⟩
  · subst n
    exact Or.inl ⟨q, hq, hdis, hlevel⟩

end PoincareConjecture.M25.Topology3D
