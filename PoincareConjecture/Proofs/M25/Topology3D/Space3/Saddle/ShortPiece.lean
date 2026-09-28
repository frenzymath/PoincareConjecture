import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.AmbientHeightCompression
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapCompressionBuffers
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerLevelHeightCompression











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "D1" => Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞




theorem exists_short_saddle_piece
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
    let c := f D.point
    let H : E3 → ℝ := fun y => ⟪(u : E3), y⟫_ℝ
    let P : E3 → E2 := fun y => (heightPlaneCoordinates u y).1
    let S := range (fun q : UnitTwoSphere => psi (q, 0))
    ∃ (h : D1) (G0 G : D3) (I : ℝ → D3) (k delta : ℝ)
      (R o w : Fin D.capCount → ℝ) (Csupport : Set E3),
    ∃ (hk : 0 < k) (hdelta : 0 < delta)
      (hmono : StrictMono (fun z => h z))
      (hfix : ∀ z, |z - c| ≤ delta → h z = z)
      (hG0 : ∀ y : E3, H (G0 y) = h (H y))
      (hRadius : ∀ i, D.cutRadius i ≤ R i)
      (hWidths : ∀ i, 0 < o i ∧ o i ≤ (D.cap i).overlapWidth / 4 ∧
        0 < w i ∧ w i ≤ (D.cap i).collarWidth / 4)
      (hAffine : ∀ i z, |z - (D.cap i).cutHeight| ≤ R i → h z = c + k * (z - c))
      (hCap : ∀ i (q : UnitTwoSphere), (heightCoordinates (q : E3)).2 ≤ 2 * o i →
        |(D.cap i).cutHeight + (D.cap i).sign *
            ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model q).2) -
          (D.cap i).cutHeight| ≤ R i)
      (hCol : ∀ i s, |s| ≤ 2 * w i →
        |(D.cap i).cutHeight + (D.cap i).sign * ((D.cap i).removal - (D.cap i).scale) +
          (D.cap i).beta * s - (D.cap i).cutHeight| ≤ R i)
      (hAgree : EqOn G G0 (S ∪ ⋃ i, (D.cap i).tube ''
        (closedBall (0 : E2) 1 ×ˢ closedBall (D.cap i).cutHeight (R i))))
      (hPlanar : ∀ y : E3, P (G y) = P y),
    let psiNew := fun p => G (psi p)
    let Dbar := D.heightCompress hpsi h G0 G k delta R o w hk hdelta hmono
      hfix hG0 hRadius hWidths hAffine hCap hCol hAgree
    let Rh := (Diffeomorph.refl (𝓡 1) UnitCircle ∞).prodCongr h.symm
    ∃ Dnew : SaddlePieceData psiNew u,
      Dnew = Dbar ∧ k ≤ 1 / 2 ∧
      (∀ y, H (G0 y) = h (H y) ∧ P (G0 y) = P y) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => I p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (I p.1).symm p.2) ∧
      (∀ y, I 0 y = y) ∧ I 1 = G ∧
      (∀ s y, (I s).symm y = I (-s) y) ∧
      (∀ s y, P (I s y) = P y) ∧ IsCompact Csupport ∧
      (∀ s, tsupport (fun y => I s y - y) ⊆ Csupport ∧
        tsupport (fun y => (I s).symm y - y) ⊆ Csupport) ∧
      (∀ y, |H y - c| ≤ delta → G0 y = y ∧ ∀ s, I s y = y) ∧
      (∀ s, IsCollarEmbedding (fun p => I s (psi p))) ∧
      (∀ p, G.symm (psiNew p) = psi p) ∧ IsCollarEmbedding psiNew ∧
      range (fun q : UnitTwoSphere => psiNew (q, 0)) = G '' S ∧
      G.symm '' range (fun q : UnitTwoSphere => psiNew (q, 0)) = S ∧
      (∀ q : UnitTwoSphere, |H (psiNew (q, 0)) - c| < epsilon) ∧
      (∀ q : UnitTwoSphere, H (psiNew (q, 0)) = h (f q)) ∧
      (∀ q : UnitTwoSphere,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => H (psiNew (p, 0))) q = 0 ↔
          mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0) ∧
      H (psiNew (Dnew.point, 0)) = c ∧
      (∀ q ∈ Dnew.morse.source, ∀ s, I s (psi (q, 0)) = psi (q, 0)) ∧
      (∀ q ∈ closure Dnew.protectedSet, ∀ s, I s (psi (q, 0)) = psi (q, 0)) ∧
      (∀ i,
        h '' Icc ((D.cap i).cutHeight - D.cutRadius i)
            ((D.cap i).cutHeight + D.cutRadius i) =
          Icc (h (D.cap i).cutHeight - k * D.cutRadius i)
            (h (D.cap i).cutHeight + k * D.cutRadius i) ∧
        (Dbar.cap i).tube '' (closedBall (0 : E2) 1 ×ˢ
            Icc (h (D.cap i).cutHeight - k * D.cutRadius i)
              (h (D.cap i).cutHeight + k * D.cutRadius i)) =
          G '' ((D.cap i).tube '' (closedBall (0 : E2) 1 ×ˢ
            Icc ((D.cap i).cutHeight - D.cutRadius i)
              ((D.cap i).cutHeight + D.cutRadius i)))) ∧
      (∀ W : SaddleLowerLevelData D,
        ∃ Wnew : SaddleLowerLevelData Dnew,
          HEq Wnew (W.heightCompress hpsi h G0 G k delta R o w hk hdelta hmono
            hfix hG0 hRadius hWidths hAffine hCap hCol hAgree hPlanar) ∧
          Wnew.level = h W.level ∧ HEq Wnew.label W.label ∧
          (∀ b, Wnew.disc b = W.disc b) ∧
          ∀ b,
            Wnew.leg b = Rh.toHomeomorph.toOpenPartialHomeomorph.trans (W.leg b) ∧
            (Wnew.leg b).source = {p : UnitCircle × ℝ |
              (p.1, h.symm p.2) ∈ (W.leg b).source} ∧
            (Wnew.leg b).target = (W.leg b).target ∧
            (∀ p : UnitCircle × ℝ, Wnew.leg b p = W.leg b (p.1, h.symm p.2)) ∧
            (∀ q : UnitTwoSphere, (Wnew.leg b).symm q =
              (((W.leg b).symm q).1, h ((W.leg b).symm q).2)) ∧
            Wnew.leg b '' (univ ×ˢ Icc
                (h ((D.cap (W.label b)).cutHeight +
                  (D.cap (W.label b)).sign * (D.cap (W.label b)).removal)) (h W.level)) =
              W.leg b '' (univ ×ˢ Icc ((D.cap (W.label b)).cutHeight +
                (D.cap (W.label b)).sign * (D.cap (W.label b)).removal) W.level)) ∧
      (D.nonnested → Dnew.nonnested) ∧ (D.nested → Dnew.nested) := by
  let f : UnitTwoSphere → ℝ := fun q => ⟪(u : E3), psi (q, 0)⟫_ℝ
  let c := f D.point
  let H : E3 → ℝ := fun y => ⟪(u : E3), y⟫_ℝ
  let P : E3 → E2 := fun y => (heightPlaneCoordinates u y).1
  let S := range (fun q : UnitTwoSphere => psi (q, 0))
  obtain ⟨o, w, R, hbuf, hsets⟩ := exists_finite_surgeryCap_compression_buffers
    psi hpsi u c D.capCount D.cap D.cutRadius D.removal_lt_cutRadius D.cutRadius_lt_gap
  let J := ⋃ i, closedBall (D.cap i).cutHeight (R i)
  let Q := psi '' (univ ×ˢ ({0} : Set ℝ)) ∪ ⋃ i, (D.cap i).tube ''
    (closedBall (0 : E2) 1 ×ˢ closedBall (D.cap i).cutHeight (R i))
  rcases hsets with ⟨hJ, hcJ, hQ, hcentral, htracks⟩
  have hS : psi '' (univ ×ˢ ({0} : Set ℝ)) = S := by
    ext y
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      obtain rfl : t = 0 := ht
      exact mem_range_self q
    · rintro ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have hSQ : Q = S ∪ ⋃ i, (D.cap i).tube ''
      (closedBall (0 : E2) 1 ×ˢ closedBall (D.cap i).cutHeight (R i)) := by
    exact congrArg (fun A => A ∪ ⋃ i, (D.cap i).tube ''
      (closedBall (0 : E2) 1 ×ˢ closedBall (D.cap i).cutHeight (R i))) hS
  obtain ⟨h, G0, G, I, k, delta, a, Csupport, hk, hkhalf, hdelta, _,
      hplanBound, hmono, hnear, hfix, hcoords, hcyl, hfixed, hI, hInv,
      hzero, hone, hneg, hplanar, hcompact, hsupport, hshort⟩ :=
    exists_compact_ambient_height_compression u c hQ hJ hcJ hepsilon
  have hG0 (y : E3) : H (G0 y) = h (H y) := (hcoords y).1
  have hRadius (i : Fin D.capCount) : D.cutRadius i ≤ R i := by
    rcases hbuf i with ⟨_, _, _, _, _, _, _, hi, _⟩
    exact hi
  have hWidths (i : Fin D.capCount) :
      0 < o i ∧ o i ≤ (D.cap i).overlapWidth / 4 ∧
        0 < w i ∧ w i ≤ (D.cap i).collarWidth / 4 := by
    rcases hbuf i with ⟨ho, hoo, _, hw, hww, _⟩
    exact ⟨ho, hoo, hw, hww⟩
  have hAffine (i : Fin D.capCount) (z : ℝ)
      (hz : |z - (D.cap i).cutHeight| ≤ R i) : h z = c + k * (z - c) :=
    subset_of_mem_nhdsSet hnear ((htracks i).1
      (by simpa only [mem_closedBall, Real.dist_eq] using hz))
  have hCap (i : Fin D.capCount) (q : UnitTwoSphere)
      (hq : (heightCoordinates (q : E3)).2 ≤ 2 * o i) :
      |(D.cap i).cutHeight + (D.cap i).sign *
          ((D.cap i).removal + (D.cap i).scale * ((D.cap i).profile.model q).2) -
        (D.cap i).cutHeight| ≤ R i := by
    rcases hbuf i with ⟨_, _, _, _, _, _, _, _, _, hi, _⟩
    exact hi q hq
  have hCol (i : Fin D.capCount) (s : ℝ) (hs : |s| ≤ 2 * w i) :
      |(D.cap i).cutHeight + (D.cap i).sign * ((D.cap i).removal - (D.cap i).scale) +
        (D.cap i).beta * s - (D.cap i).cutHeight| ≤ R i := by
    rcases hbuf i with ⟨_, _, _, _, _, _, _, _, _, _, hi⟩
    exact hi s hs
  have hAgree : EqOn G G0 (S ∪ ⋃ i, (D.cap i).tube ''
      (closedBall (0 : E2) 1 ×ˢ closedBall (D.cap i).cutHeight (R i))) := by
    intro y hy
    have hyQ : y ∈ Q := by rwa [hSQ]
    exact (hcyl y (hplanBound y hyQ).le).1
  have hPlanar (y : E3) : P (G y) = P y := by
    rw [← hone]
    exact hplanar 1 y
  let psiNew := fun p => G (psi p)
  let Dbar := D.heightCompress hpsi h G0 G k delta R o w hk hdelta hmono
    hfix hG0 hRadius hWidths hAffine hCap hCol hAgree
  let Rh := (Diffeomorph.refl (𝓡 1) UnitCircle ∞).prodCongr h.symm
  have hnew (q : UnitTwoSphere) : H (psiNew (q, 0)) = h (f q) := by
    change H (G (psi (q, 0))) = h (f q)
    rw [hAgree (Or.inl (mem_range_self q)), hG0]
  have hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f :=
    (InnerProductSpace.toDual ℝ E3 (u : E3)).contDiff.contMDiff.comp
      (collar_central_contMDiff psi hpsi)
  have hcrit (q : UnitTwoSphere) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun p : UnitTwoSphere => H (psiNew (p, 0))) q = 0 ↔
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q = 0 := by
    have hfun : (fun q : UnitTwoSphere => H (psiNew (q, 0))) = (h : ℝ → ℝ) ∘ f :=
      funext hnew
    have hhinj := (h.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (x := f q) (mem_univ _)
    rw [hfun, mfderiv_comp q (h.mdifferentiable (by simp) (f q))
      (hf.mdifferentiable (by simp) q)]
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) h (f q) : ℝ →L[ℝ] ℝ).comp
        (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q : TangentSpace (𝓡 2) q →L[ℝ] ℝ) = 0 ↔
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f q : TangentSpace (𝓡 2) q →L[ℝ] ℝ) = 0
    constructor
    · intro hz
      ext v
      apply hhinj
      exact (congrArg (fun A => A v) hz).trans
        (map_zero (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) h (f q))).symm
    · intro hz
      simp only [hz, ContinuousLinearMap.comp_zero]
  have hIcc (a b z : ℝ) : z ∈ Icc (h a) (h b) ↔ h.symm z ∈ Icc a b := by
    constructor
    · intro hz
      exact ⟨hmono.le_iff_le.mp (by simpa only [h.apply_symm_apply] using hz.1),
        hmono.le_iff_le.mp (by simpa only [h.apply_symm_apply] using hz.2)⟩
    · intro hz
      exact ⟨by simpa only [h.apply_symm_apply] using hmono.monotone hz.1,
        by simpa only [h.apply_symm_apply] using hmono.monotone hz.2⟩
  have himage (a b : ℝ) : h '' Icc a b = Icc (h a) (h b) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨hmono.monotone ht.1, hmono.monotone ht.2⟩
    · intro hz
      exact ⟨h.symm z, (hIcc a b z).mp hz, h.apply_symm_apply z⟩
  have hwin (i : Fin D.capCount) (z : ℝ)
      (hz : z ∈ Icc ((D.cap i).cutHeight - D.cutRadius i)
        ((D.cap i).cutHeight + D.cutRadius i)) :
      |z - (D.cap i).cutHeight| ≤ R i := by
    apply abs_le.mpr
    constructor <;> linarith [hz.1, hz.2, hRadius i]
  have hinterval (i : Fin D.capCount) :
      h '' Icc ((D.cap i).cutHeight - D.cutRadius i)
          ((D.cap i).cutHeight + D.cutRadius i) =
        Icc (h (D.cap i).cutHeight - k * D.cutRadius i)
          (h (D.cap i).cutHeight + k * D.cutRadius i) := by
    have hd : 0 < D.cutRadius i := (D.cap i).removal_pos.trans (D.removal_lt_cutRadius i)
    have hm := hAffine i (D.cap i).cutHeight
      (by simpa only [sub_self, abs_zero] using hd.le.trans (hRadius i))
    have hlo := hAffine i _ (hwin i _ ⟨le_rfl, by linarith⟩)
    have hhi := hAffine i _ (hwin i _ ⟨by linarith, le_rfl⟩)
    rw [himage, hlo, hhi, hm]
    congr 1 <;> ring
  have hsourceFixed (q : UnitTwoSphere) (hq : q ∈ Dbar.morse.source) (s : ℝ) :
      I s (psi (q, 0)) = psi (q, 0) :=
    (hfixed (psi (q, 0)) hq.2.le).2 s
  have hnewRange : range (fun q : UnitTwoSphere => psiNew (q, 0)) = G '' S :=
    range_comp' (fun y : E3 => G y) (fun q : UnitTwoSphere => psi (q, 0))
  refine ⟨h, G0, G, I, k, delta, R, o, w, Csupport, hk, hdelta, hmono, hfix,
    hG0, hRadius, hWidths, hAffine, hCap, hCol, hAgree, hPlanar,
    Dbar, rfl, hkhalf, hcoords, hI, hInv, hzero, hone, hneg, hplanar, hcompact,
    ?_, hfixed, (fun s => hpsi.postcompose_diffeomorph (I s)),
    (fun p => G.symm_apply_apply (psi p)), hpsi.postcompose_diffeomorph G,
    hnewRange, ?_, ?_, hnew, hcrit, ?_, hsourceFixed, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    refine ⟨hsupport s, ?_⟩
    simpa only [hneg] using hsupport (-s)
  · rw [hnewRange, image_image]
    change (fun y => G.symm (G y)) '' S = S
    simp only [G.symm_apply_apply, image_id']
  · intro q
    apply hshort (psi (q, 0))
    change psi (q, 0) ∈ Q
    rw [hSQ]
    exact Or.inl (mem_range_self q)
  · change H (psiNew (D.point, 0)) = c
    rw [hnew]
    exact hfix c (by simpa only [sub_self, abs_zero] using hdelta.le)
  · intro q hq s
    exact hsourceFixed q (Dbar.protected_closure hq).1 s
  · intro i
    refine ⟨hinterval i, ?_⟩
    change heightTransportTube (D.cap i).tube h G0 ''
      (closedBall (0 : E2) 1 ×ˢ Icc (h (D.cap i).cutHeight - k * D.cutRadius i)
        (h (D.cap i).cutHeight + k * D.cutRadius i)) = _
    rw [← hinterval i]
    ext y
    constructor
    · rintro ⟨⟨x, z⟩, hp, rfl⟩
      obtain ⟨t, ht, rfl⟩ := hp.2
      refine ⟨(D.cap i).tube (x, t), ⟨(x, t), ⟨hp.1, ht⟩, rfl⟩, ?_⟩
      rw [heightTransportTube_apply, h.symm_apply_apply]
      exact hAgree (Or.inr (mem_iUnion.mpr ⟨i, ⟨(x, t), ⟨hp.1,
        by simpa only [mem_closedBall, Real.dist_eq] using hwin i t ht⟩, rfl⟩⟩))
    · rintro ⟨_, ⟨⟨x, t⟩, hp, rfl⟩, rfl⟩
      refine ⟨(x, h t), ⟨hp.1, ⟨t, hp.2, rfl⟩⟩, ?_⟩
      rw [heightTransportTube_apply, h.symm_apply_apply]
      exact (hAgree (Or.inr (mem_iUnion.mpr ⟨i, ⟨(x, t), ⟨hp.1,
        by simpa only [mem_closedBall, Real.dist_eq] using hwin i t hp.2⟩, rfl⟩⟩))).symm
  · intro W
    let Wnew := W.heightCompress hpsi h G0 G k delta R o w hk hdelta hmono
      hfix hG0 hRadius hWidths hAffine hCap hCol hAgree hPlanar
    refine ⟨Wnew, HEq.rfl, rfl, HEq.rfl, (fun _ => rfl), ?_⟩
    intro b
    refine ⟨rfl, ?_, ?_, (fun _ => rfl), (fun _ => rfl), ?_⟩
    · ext p
      change (True ∧ (p.1, h.symm p.2) ∈ (W.leg b).source) ↔ _
      simp only [true_and, mem_ofPred_eq]
    · ext q
      change (q ∈ (W.leg b).target ∧ True) ↔ q ∈ (W.leg b).target
      simp only [and_true]
    · ext q
      constructor
      · rintro ⟨⟨theta, z⟩, hp, rfl⟩
        exact ⟨(theta, h.symm z), ⟨mem_univ _, (hIcc _ _ _).mp hp.2⟩, rfl⟩
      · rintro ⟨⟨theta, z⟩, hp, rfl⟩
        refine ⟨(theta, h z), ⟨mem_univ _, hmono.monotone hp.2.1,
          hmono.monotone hp.2.2⟩, ?_⟩
        change W.leg b (theta, h.symm (h z)) = W.leg b (theta, z)
        rw [h.symm_apply_apply]
  · rintro ⟨W, hW⟩
    exact ⟨W.heightCompress hpsi h G0 G k delta R o w hk hdelta hmono
      hfix hG0 hRadius hWidths hAffine hCap hCol hAgree hPlanar, hW⟩
  · rintro ⟨W, hW⟩
    exact ⟨W.heightCompress hpsi h G0 G k delta R o w hk hdelta hmono
      hfix hG0 hRadius hWidths hAffine hCap hCol hAgree hPlanar, hW⟩

end PoincareConjecture.M25.Topology3D
