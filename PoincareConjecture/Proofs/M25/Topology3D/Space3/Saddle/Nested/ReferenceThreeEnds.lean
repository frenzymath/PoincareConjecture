import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceNativeThreeEnds
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceThreeCutRelocation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_saddle_nested_reference_three_ends
    (u : UnitTwoSphere) (ws wm d Lambda c : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32))
    (hLambda : 0 < Lambda) (A : D3)
    (hA : ∀ y : E3, ⟪(u : E3), A y⟫_ℝ =
      c + Lambda * ((heightCoordinates y).2 -
        (1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32) - d))
    (P : SurgeryCapProfile) (z v tau : ℝ)
    (hlow : c - Lambda * ((1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32) - 17 / 16) < z)
    (hzc : z < c) (hcv : c < v)
    (hup : v < c + Lambda * ((1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32) -
      (1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32)))
    (htau : 0 < tau) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let Sp : Set E3 := A '' (nestedReferenceBallChart d).boundary
    ∃ tgap : ℝ, 0 < tgap ∧ tgap < tau ∧
      ∀ t : ℝ, z - tgap < t → t < z →
      let cut : Fin 3 → ℝ := ![z, t, v]
      let sign : Fin 3 → ℝ := ![1, 1, -1]
      ∃ (b : ℝ) (T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3),
        0 < b ∧ 4 * b < tau ∧ 4 * b < z - t ∧ 4 * b < c - z ∧ 4 * b < v - c ∧
        (∀ k : Fin 3,
          closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T k).source ∧
          ContDiffOn ℝ ∞ (T k) (T k).source ∧
          ContDiffOn ℝ ∞ (T k).symm (T k).target ∧
          (∀ x ∈ (T k).source, H (T k x) = x.2) ∧
          (∀ y ∈ (T k).target, ((T k).symm y).2 = H y)) ∧
        (∀ s ∈ Icc (t - 4 * b) (z + 4 * b),
          Sp ∩ {y : E3 | H y = s} =
            T 0 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
              T 1 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
          T 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
            T 1 '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ))) ∧
        (∀ s ∈ Icc (v - 4 * b) (v + 4 * b),
          T 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) =
            Sp ∩ {y : E3 | H y = s}) ∧
        ∀ lambda : Fin 3 → ℝ, (∀ k, 0 < lambda k) →
          (∀ k, lambda k * P.heightBound < b) →
          let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          let cap : Fin 3 → Set E3 := fun k =>
            P.capMap (T k) (cut k) (sign k) 0 (lambda k) '' Qminus
          let Lcyl : Set E3 := T 1 '' (sphere (0 : E2) 1 ×ˢ Icc t z)
          let M : Set E3 := (Sp ∩ {y | z ≤ H y ∧ H y ≤ v}) ∪ Lcyl
          ∃ G : D3,
            G '' Sp = M ∪ ⋃ k : Fin 3, cap k ∧
            G.symm '' (M ∪ ⋃ k : Fin 3, cap k) = Sp ∧
            (∀ y ∈ M, G y = y ∧ G.symm y = y) ∧
            (∀ (k : Fin 3) (y : E3), y ∈ cap k →
              |H y - cut k| ≤ lambda k * P.heightBound) := by
  classical
  intro H Sp
  let H0 : E3 → ℝ := fun y => (heightCoordinates y).2
  let S0 : Set E3 := (nestedReferenceBallChart d).boundary
  let U : E2 → ℝ := fun x => ‖x‖ ^ 2 + Real.sqrt (1 - ‖x‖ ^ 2) + x 0 / 32
  let k := 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32
  let mu := 1 - wm ^ 2 + wm + Real.sqrt (1 - wm ^ 2) / 32
  let alpha : ℝ := 17 / 16 + 1 / 131072
  let beta : ℝ := 17 / 16 + 1 / 65536
  obtain ⟨nu, eta, T0, hbk, hknu, hnumu, heta, hT0, hLo0, hUp0, hEx0⟩ :=
    NestedReferenceLower.exists_reference_native_three_ends ws wm d
      hwslo hwshi hwsroot hwmlo hwmhi hwmroot
  change beta < k at hbk
  change k < nu at hknu
  change nu < mu at hnumu
  obtain ⟨b0, hb0, hExchange⟩ := hEx0 P
  let low := c - Lambda * (k - 17 / 16)
  change low < z at hlow
  change v < c + Lambda * (mu - k) at hup
  let gap := min tau (z - low)
  have hgap : 0 < gap := lt_min htau (sub_pos.mpr hlow)
  have hgaptau : gap ≤ tau := min_le_left _ _
  have hgaplow : gap ≤ z - low := min_le_right _ _
  refine ⟨gap / 2, half_pos hgap, by linarith only [hgap, hgaptau], ?_⟩
  intro t ht htz cut sign
  have hlt : low < t := by linarith only [ht, hgap, hgaplow]
  let nt := k + (t - c) / Lambda
  let nz := k + (z - c) / Lambda
  let nv := k + (v - c) / Lambda
  have hLt : Lambda * (nt - k) = t - c := by
    dsimp only [nt]
    field_simp [hLambda.ne']
    ring
  have hLz : Lambda * (nz - k) = z - c := by
    dsimp only [nz]
    field_simp [hLambda.ne']
    ring
  have hLv : Lambda * (nv - k) = v - c := by
    dsimp only [nv]
    field_simp [hLambda.ne']
    ring
  have hnt : 17 / 16 < nt := by
    change c - Lambda * (k - 17 / 16) < t at hlt
    nlinarith only [hlt, hLt, hLambda]
  have hntz : nt < nz := by nlinarith only [hLt, hLz, htz, hLambda]
  have hnzk : nz < k := by nlinarith only [hLz, hzc, hLambda]
  have hknv : k < nv := by nlinarith only [hLv, hcv, hLambda]
  have hnvmu : nv < mu := by nlinarith only [hLv, hup, hLambda]
  have hksq : ‖(!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2)‖ ^ 2 = 1 - ws ^ 2 := by
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using
      Real.sq_sqrt (show 0 ≤ 1 - ws ^ 2 by nlinarith only [hwslo, hwshi])
  have hmsq : ‖(!₂[Real.sqrt (1 - wm ^ 2), 0] : E2)‖ ^ 2 = 1 - wm ^ 2 := by
    simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using
      Real.sq_sqrt (show 0 ≤ 1 - wm ^ 2 by nlinarith only [hwmlo, hwmhi])
  have hUk : U !₂[-Real.sqrt (1 - ws ^ 2), 0] = k := by
    change ‖(!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2)‖ ^ 2 +
      Real.sqrt (1 - ‖(!₂[-Real.sqrt (1 - ws ^ 2), 0] : E2)‖ ^ 2) +
      -Real.sqrt (1 - ws ^ 2) / 32 = k
    rw [hksq, show 1 - (1 - ws ^ 2) = ws ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_pos (by linarith only [hwslo])]
    dsimp only [k]
    ring
  have hUm : U !₂[Real.sqrt (1 - wm ^ 2), 0] = mu := by
    change ‖(!₂[Real.sqrt (1 - wm ^ 2), 0] : E2)‖ ^ 2 +
      Real.sqrt (1 - ‖(!₂[Real.sqrt (1 - wm ^ 2), 0] : E2)‖ ^ 2) +
      Real.sqrt (1 - wm ^ 2) / 32 = mu
    rw [hmsq, show 1 - (1 - wm ^ 2) = wm ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_pos hwmlo]
  have hRel := NestedReferenceLower.exists_reference_three_cut_relocation
    ws wm d alpha beta nu nt nz nv hwslo hwshi hwsroot hwmlo hwmhi hwmroot
  dsimp only at hRel
  dsimp only [U] at hUk hUm
  rw [hUk, hUm] at hRel
  obtain ⟨eO, eI, eU, sig, g, K, C, heO, heI, heU, _hsig, _hcC, _hC, _hdC,
    hgm, _hgim, _hgf, _hKf, hKH, _hKS, hKS, _hKiS, _hKi, _hKii,
    _hKc, _hKic, hO, hI, hU, _hLevels⟩ :=
    hRel ⟨by norm_num [alpha], by norm_num [alpha, beta], hbk⟩
      ⟨hnt, hntz, hnzk⟩ ⟨hknu, hnumu⟩ ⟨hknv, hnvmu⟩
  let h : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toEquiv := {
      toFun := fun s => c + Lambda * (s - k - d)
      invFun := fun s => k + d + (s - c) / Lambda
      left_inv := by intro s; field_simp [hLambda.ne']; ring
      right_inv := by intro s; field_simp [hLambda.ne']; ring }
    contMDiff_toFun :=
      (contDiff_const.add (contDiff_const.mul
        ((contDiff_id.sub contDiff_const).sub contDiff_const))).contMDiff
    contMDiff_invFun :=
      (contDiff_const.add ((contDiff_id.sub contDiff_const).div_const Lambda)).contMDiff }
  let f := g.trans h
  let J := K.trans A
  have hf (s : ℝ) : f s = c + Lambda * (g s - k - d) := rfl
  have hfm : StrictMono f := by
    intro a b hab
    change c + Lambda * (g a - k - d) < c + Lambda * (g b - k - d)
    simpa only [add_comm] using add_lt_add_left (mul_lt_mul_of_pos_left
      (sub_lt_sub_right (sub_lt_sub_right (hgm hab) k) d) hLambda) c
  have hJH (y : E3) : H (J y) = f (H0 y) := by
    change ⟪(u : E3), A (K y)⟫_ℝ = _
    rw [hA]
    change c + Lambda * (H0 (K y) - k - d) = _
    have hy : H0 (K y) = g (H0 y) := (hKH y).1
    rw [hy]
    rfl
  have hJS : J '' S0 = Sp := by
    change (A ∘ K) '' S0 = A '' S0
    rw [image_comp, hKS]
  let old : Fin 3 → ℝ := ![beta + d, alpha + d, nu + d]
  let mid : Fin 3 → ℝ := ![d + nz, d + nt, d + nv]
  let width : Fin 3 → ℝ := ![eI, eO, eU]
  have hwidth (j : Fin 3) : 0 < width j := by
    fin_cases j
    · exact heI
    · exact heO
    · exact heU
  have hgcut (j : Fin 3) (a : ℝ) (ha : |a| ≤ width j) :
      g (old j + a) = mid j + a := by
    fin_cases j
    · change g (beta + d + a) = d + nz + a
      simpa only [add_comm beta d] using (hI a ha).1
    · change g (alpha + d + a) = d + nt + a
      simpa only [add_comm alpha d] using (hO a ha).1
    · change g (nu + d + a) = d + nv + a
      simpa only [add_comm nu d] using (hU a ha).1
  have hmcut (j : Fin 3) : c + Lambda * (mid j - k - d) = cut j := by
    fin_cases j
    · change c + Lambda * (d + nz - k - d) = z
      nlinarith only [hLz]
    · change c + Lambda * (d + nt - k - d) = t
      nlinarith only [hLt]
    · change c + Lambda * (d + nv - k - d) = v
      nlinarith only [hLv]
  have hfcut (j : Fin 3) : f (old j) = cut j := by
    have hg := hgcut j 0 (by simpa only [abs_zero] using (hwidth j).le)
    simp only [add_zero] at hg
    rw [hf, hg, hmcut]
  have hfb : f (beta + d) = z := hfcut 0
  have hfa : f (alpha + d) = t := hfcut 1
  have hfu : f (nu + d) = v := hfcut 2
  let l0 := t - f (alpha + d - eta)
  let l1 := f (beta + d + eta) - z
  let u0 := v - f (nu + d - eta)
  let u1 := f (nu + d + eta) - v
  have hl0 : 0 < l0 := by
    dsimp only [l0]
    rw [← hfa]
    exact sub_pos.mpr (hfm (sub_lt_self _ heta))
  have hl1 : 0 < l1 := by
    dsimp only [l1]
    rw [← hfb]
    exact sub_pos.mpr (hfm (lt_add_of_pos_right _ heta))
  have hu0 : 0 < u0 := by
    dsimp only [u0]
    rw [← hfu]
    exact sub_pos.mpr (hfm (sub_lt_self _ heta))
  have hu1 : 0 < u1 := by
    dsimp only [u1]
    rw [← hfu]
    exact sub_pos.mpr (hfm (lt_add_of_pos_right _ heta))
  let m := min tau (min (z - t) (min (c - z) (min (v - c)
    (min l0 (min l1 (min u0 (min u1
      (min (Lambda * b0) (min (Lambda * eO) (min (Lambda * eI) (Lambda * eU)))))))))))
  have hm : 0 < m := lt_min htau (lt_min (sub_pos.mpr htz)
    (lt_min (sub_pos.mpr hzc) (lt_min (sub_pos.mpr hcv)
      (lt_min hl0 (lt_min hl1 (lt_min hu0 (lt_min hu1
        (lt_min (mul_pos hLambda hb0) (lt_min (mul_pos hLambda heO)
          (lt_min (mul_pos hLambda heI) (mul_pos hLambda heU)))))))))))
  have hms : m ≤ tau ∧ m ≤ z - t ∧ m ≤ c - z ∧ m ≤ v - c ∧
      m ≤ l0 ∧ m ≤ l1 ∧ m ≤ u0 ∧ m ≤ u1 ∧
      m ≤ Lambda * b0 ∧ m ≤ Lambda * eO ∧ m ≤ Lambda * eI ∧ m ≤ Lambda * eU := by
    have hh : m ≤ min tau (min (z - t) (min (c - z) (min (v - c)
        (min l0 (min l1 (min u0 (min u1
          (min (Lambda * b0) (min (Lambda * eO) (min (Lambda * eI) (Lambda * eU))))))))))) :=
      le_rfl
    simpa only [le_min_iff] using hh
  obtain ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11⟩ := hms
  let b := m / 8
  have hb : 0 < b := div_pos hm (by norm_num)
  have hbLess (a : ℝ) (ha : m ≤ a) : b < a ∧ 4 * b < a := by
    dsimp only [b]
    constructor <;> linarith only [hm, ha]
  have hbNative : b < Lambda * b0 := (hbLess _ hm8).1
  have hbWidth (j : Fin 3) : b < Lambda * width j := by
    fin_cases j
    · exact (hbLess _ hm10).1
    · exact (hbLess _ hm9).1
    · exact (hbLess _ hm11).1
  let T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3 := fun j =>
    heightTransportTube (T0 j) f J
  have hTH (j : Fin 3) (p : E2 × ℝ) (hp : p ∈ (T j).source) : H (T j p) = p.2 := by
    change H (J (T0 j (p.1, f.symm p.2))) = p.2
    have hh : H0 (T0 j (p.1, f.symm p.2)) = f.symm p.2 :=
      (hT0 j).2.2.2.1 _ ((heightTransportTube_mem_source (T0 j) f J p).mp hp)
    rw [hJH, hh]
    exact f.apply_symm_apply p.2
  have hTd (j : Fin 3) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T j).source ∧
      ContDiffOn ℝ ∞ (T j) (T j).source ∧
      ContDiffOn ℝ ∞ (T j).symm (T j).target ∧
      (∀ p ∈ (T j).source, H (T j p) = p.2) ∧
      (∀ y ∈ (T j).target, ((T j).symm y).2 = H y) := by
    refine ⟨heightTransportTube_closedDisc_source (T0 j) f J (hT0 j).1,
      heightTransportTube_contDiffOn (T0 j) f J (hT0 j).2.1,
      heightTransportTube_contDiffOn_symm (T0 j) f J (hT0 j).2.2.1, hTH j, ?_⟩
    intro y hy
    have hz := hTH j ((T j).symm y) ((T j).map_target hy)
    rw [(T j).right_inv hy] at hz
    exact hz.symm
  have hTube (j : Fin 3) (X : Set E2) (I : Set ℝ) :
      J '' (T0 j '' (X ×ˢ I)) = T j '' (X ×ˢ (f '' I)) := by
    ext y
    constructor
    · rintro ⟨w, ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩, rfl⟩
      exact ⟨(x, f s), ⟨hx, ⟨s, hs, rfl⟩⟩,
        heightTransportTube_reparametrized_apply (T0 j) f J (x, s)⟩
    · rintro ⟨⟨x, s⟩, ⟨hx, r, hr, hrs⟩, rfl⟩
      change f r = s at hrs
      subst s
      refine ⟨T0 j (x, r), ⟨(x, r), ⟨hx, hr⟩, rfl⟩, ?_⟩
      exact (heightTransportTube_reparametrized_apply (T0 j) f J (x, r)).symm
  have hIcc (a b : ℝ) : f '' Icc a b = Icc (f a) (f b) := by
    ext s
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨hfm.monotone hr.1, hfm.monotone hr.2⟩
    · intro hs
      refine ⟨f.symm s, ⟨?_, ?_⟩, f.apply_symm_apply s⟩
      · apply hfm.le_iff_le.mp
        simpa only [f.apply_symm_apply] using hs.1
      · apply hfm.le_iff_le.mp
        simpa only [f.apply_symm_apply] using hs.2
  have hSlice (s : ℝ) :
      J '' (S0 ∩ {y | H0 y = f.symm s}) = Sp ∩ {y | H y = s} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hhx⟩, rfl⟩
      refine ⟨hJS ▸ mem_image_of_mem J hx, ?_⟩
      change H (J x) = s
      rw [hJH, hhx, f.apply_symm_apply]
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hJS.symm ▸ hy.1
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      apply f.injective
      change f (H0 x) = f (f.symm s)
      rw [f.apply_symm_apply, ← hJH]
      exact hy.2
  have hTubeSlice (j : Fin 3) (X : Set E2) (s : ℝ) :
      J '' (T0 j '' (X ×ˢ ({f.symm s} : Set ℝ))) = T j '' (X ×ˢ ({s} : Set ℝ)) := by
    rw [hTube, image_singleton, f.apply_symm_apply]
  have hLoWin (s : ℝ) (hs : s ∈ Icc (t - 4 * b) (z + 4 * b)) :
      f.symm s ∈ Icc (alpha + d - eta) (beta + d + eta) := by
    have ha := (hbLess _ hm4).2
    have hz := (hbLess _ hm5).2
    change 4 * b < t - f (alpha + d - eta) at ha
    change 4 * b < f (beta + d + eta) - z at hz
    constructor
    · apply hfm.le_iff_le.mp
      rw [f.apply_symm_apply]
      linarith only [hs.1, ha]
    · apply hfm.le_iff_le.mp
      rw [f.apply_symm_apply]
      linarith only [hs.2, hz]
  have hUpWin (s : ℝ) (hs : s ∈ Icc (v - 4 * b) (v + 4 * b)) :
      f.symm s ∈ Icc (nu + d - eta) (nu + d + eta) := by
    have ha := (hbLess _ hm6).2
    have hz := (hbLess _ hm7).2
    change 4 * b < v - f (nu + d - eta) at ha
    change 4 * b < f (nu + d + eta) - v at hz
    constructor
    · apply hfm.le_iff_le.mp
      rw [f.apply_symm_apply]
      linarith only [hs.1, ha]
    · apply hfm.le_iff_le.mp
      rw [f.apply_symm_apply]
      linarith only [hs.2, hz]
  have hLower (s : ℝ) (hs : s ∈ Icc (t - 4 * b) (z + 4 * b)) :
      Sp ∩ {y : E3 | H y = s} =
        T 0 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∪
          T 1 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ∧
      T 0 '' (closedBall (0 : E2) 1 ×ˢ ({s} : Set ℝ)) ⊆
        T 1 '' (ball (0 : E2) 1 ×ˢ ({s} : Set ℝ)) := by
    obtain ⟨hlevel, hfill⟩ := hLo0 (f.symm s) (hLoWin s hs)
    constructor
    · rw [← hSlice, hlevel, image_union, hTubeSlice, hTubeSlice]
    · rw [← hTubeSlice, ← hTubeSlice]
      exact image_mono hfill
  have hUpper (s : ℝ) (hs : s ∈ Icc (v - 4 * b) (v + 4 * b)) :
      T 2 '' (sphere (0 : E2) 1 ×ˢ ({s} : Set ℝ)) = Sp ∩ {y | H y = s} := by
    rw [← hTubeSlice, hUp0 (f.symm s) (hUpWin s hs), hSlice]
  refine ⟨b, T, hb, (hbLess _ hm0).2, (hbLess _ hm1).2,
    (hbLess _ hm2).2, (hbLess _ hm3).2, hTd, hLower, hUpper, ?_⟩
  intro lambda hlambda hsmall Qminus cap Lcyl M
  let lambda0 : Fin 3 → ℝ := fun j => lambda j / Lambda
  have hl0pos (j : Fin 3) : 0 < lambda0 j := div_pos (hlambda j) hLambda
  have hl0Bound (j : Fin 3) (a : ℝ) (ha : b < Lambda * a) :
      lambda0 j * P.heightBound < a := by
    change (lambda j / Lambda) * P.heightBound < a
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hLambda).mpr
    simpa only [mul_comm a Lambda] using (hsmall j).trans ha
  let cap0 : Fin 3 → Set E3 := fun j =>
    P.capMap (T0 j) (old j) (sign j) 0 (lambda0 j) '' Qminus
  let M0 : Set E3 :=
    (S0 ∩ {y | beta + d ≤ H0 y ∧ H0 y ≤ nu + d}) ∪
      T0 1 '' (sphere (0 : E2) 1 ×ˢ Icc (alpha + d) (beta + d))
  obtain ⟨G0, hG0, _hG0i, hFix0, _hCap0⟩ :=
    hExchange lambda0 hl0pos (fun j => hl0Bound j b0 hbNative)
  change G0 '' S0 = M0 ∪ ⋃ j : Fin 3, cap0 j at hG0
  change ∀ y ∈ M0, G0 y = y ∧ G0.symm y = y at hFix0
  have hsign (j : Fin 3) : |sign j| = 1 := by
    fin_cases j <;> norm_num [sign]
  have hCapPoint (j : Fin 3) (q : UnitTwoSphere) :
      J (P.capMap (T0 j) (old j) (sign j) 0 (lambda0 j) q) =
        P.capMap (T j) (cut j) (sign j) 0 (lambda j) q := by
    have hoff : |sign j * (lambda0 j * (P.model q).2)| ≤ width j := by
      calc
        _ = lambda0 j * |(P.model q).2| := by
          rw [abs_mul, hsign, one_mul, abs_mul, abs_of_pos (hl0pos j)]
        _ ≤ lambda0 j * P.heightBound :=
          mul_le_mul_of_nonneg_left (P.height_bound q) (hl0pos j).le
        _ ≤ width j := (hl0Bound j (width j) (hbWidth j)).le
    have hfp : f (old j + sign j * (lambda0 j * (P.model q).2)) =
        cut j + sign j * (lambda j * (P.model q).2) := by
      rw [hf, hgcut j _ hoff]
      calc
        _ = (c + Lambda * (mid j - k - d)) +
            sign j * (lambda j * (P.model q).2) := by
          dsimp only [lambda0]
          field_simp [hLambda.ne']
          ring
        _ = _ := by rw [hmcut]
    simp only [SurgeryCapProfile.capMap_apply, zero_add]
    calc
      _ = T j ((P.model q).1, f (old j + sign j * (lambda0 j * (P.model q).2))) :=
        (heightTransportTube_reparametrized_apply (T0 j) f J
          ((P.model q).1, old j + sign j * (lambda0 j * (P.model q).2))).symm
      _ = _ := by rw [hfp]
  have hCaps (j : Fin 3) : J '' cap0 j = cap j := by
    ext y
    constructor
    · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (hCapPoint j q).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨P.capMap (T0 j) (old j) (sign j) 0 (lambda0 j) q,
        ⟨q, hq, rfl⟩, hCapPoint j q⟩
  have hBand : J '' (S0 ∩ {y | beta + d ≤ H0 y ∧ H0 y ≤ nu + d}) =
      Sp ∩ {y | z ≤ H y ∧ H y ≤ v} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, ha, hb⟩, rfl⟩
      refine ⟨hJS ▸ mem_image_of_mem J hx, ?_, ?_⟩
      · rw [hJH, ← hfb]
        exact hfm.monotone ha
      · rw [hJH, ← hfu]
        exact hfm.monotone hb
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hJS.symm ▸ hy.1
      refine ⟨x, ⟨hx, ?_, ?_⟩, rfl⟩
      · apply hfm.le_iff_le.mp
        rw [hfb, ← hJH]
        exact hy.2.1
      · apply hfm.le_iff_le.mp
        rw [hfu, ← hJH]
        exact hy.2.2
  have hJM : J '' M0 = M := by
    change J '' (_ ∪ _) = _ ∪ _
    rw [image_union, hBand, hTube, hIcc, hfa, hfb]
  have hJinv (X : Set E3) : J.symm '' (J '' X) = X := by
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [J.symm_apply_apply] using hz
    · intro hy
      exact ⟨J y, ⟨y, hy, rfl⟩, J.symm_apply_apply y⟩
  let G := J.symm.trans (G0.trans J)
  have hImage : G '' Sp = M ∪ ⋃ j : Fin 3, cap j := by
    change (J ∘ G0 ∘ J.symm) '' Sp = _
    rw [image_comp, image_comp, ← hJS, hJinv, hG0, image_union, hJM, image_iUnion]
    simp_rw [hCaps]
  refine ⟨G, hImage, ?_, ?_, ?_⟩
  · rw [← hImage]
    ext y
    constructor
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      simpa only [G.symm_apply_apply] using ha
    · intro hy
      exact ⟨G y, ⟨y, hy, rfl⟩, G.symm_apply_apply y⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hJM.symm ▸ hy
    obtain ⟨h1, h2⟩ := hFix0 x hx
    change J (G0 (J.symm (J x))) = J x ∧ J (G0.symm (J.symm (J x))) = J x
    simp only [J.symm_apply_apply, h1, h2, and_self]
  · intro j y hy
    obtain ⟨q, _hq, rfl⟩ := hy
    have hs : ((P.model q).1, cut j + sign j * (0 + lambda j * (P.model q).2)) ∈
        (T j).source := (hTd j).1
      ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩
    rw [SurgeryCapProfile.capMap_apply, hTH j _ hs, zero_add, add_sub_cancel_left,
      abs_mul, hsign, one_mul, abs_mul, abs_of_pos (hlambda j)]
    exact mul_le_mul_of_nonneg_left (P.height_bound q) (hlambda j).le

end PoincareConjecture.M25.Topology3D
