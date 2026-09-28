import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapTransfer










set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D



theorem stackMorseCanonicalCap_image_eq_of_annular_match
    (u : UnitTwoSphere) (A : OpenPartialHomeomorph (E2 × ℝ) E3)
    (R : E2 ≃ₗᵢ[ℝ] E2)
    (T Q : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hQ : ContDiffOn ℝ ∞ Q Q.source)
    (hQi : ContDiffOn ℝ ∞ Q.symm Q.target)
    (hTh : ∀ p ∈ T.source, (T p).1 = p.1)
    (hQh : ∀ p ∈ Q.source, (Q p).1 = p.1)
    (c kappa rho lambda gamma delta : ℝ) (hkappa : |kappa| = 1)
    (hrho : 0 < rho) (hlambda : 0 < lambda)
    (hsmall : lambda < rho ^ 2 / 2) (hlg : lambda < gamma)
    (hdelta : 0 < delta)
    (hTsource : T.source = {p : ℝ × E2 |
      0 < kappa * (p.1 - c) ∧
        (Real.sqrt (kappa * (p.1 - c)) • R p.2, p.1) ∈ A.source})
    (hTform : ∀ p : ℝ × E2, T p =
      let y : E3 := A (Real.sqrt (kappa * (p.1 - c)) • R p.2, p.1)
      ((heightPlaneCoordinates u y).2, (heightPlaneCoordinates u y).1))
    (hTs : Icc (c + kappa * rho ^ 2 - gamma)
      (c + kappa * rho ^ 2 + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ T.source)
    (hQs : Icc (c + kappa * rho ^ 2 - gamma)
      (c + kappa * rho ^ 2 + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ Q.source)
    (hmatch : ∀ z ∈ Icc (c + kappa * rho ^ 2 - gamma)
      (c + kappa * rho ^ 2 + gamma), ∀ x : E2,
      |‖x‖ - 1| < delta → T (z, x) = Q (z, x))
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hrann : 1 - delta < rFlat)
    (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let Qminus : Set UnitTwoSphere :=
      {q | (heightCoordinates (q : E3)).2 ≤ 0}
    let distance : UnitTwoSphere → ℝ := fun q =>
      rho ^ 2 + lambda * (M (heightCoordinates (q : E3))).2
    let horizontal : UnitTwoSphere → E2 := fun q =>
      Real.sqrt (distance q) • (M (heightCoordinates (q : E3))).1
    let endpoint : UnitTwoSphere → E3 := fun q =>
      A (horizontal q, c + kappa * distance q)
    let cap : Set E3 := endpoint '' Qminus
    let s : ℝ := c + kappa * rho ^ 2
    let placed : UnitTwoSphere → ℝ × E2 := fun q =>
      (s + kappa * lambda * (M (heightCoordinates (q : E3))).2,
        (M (heightCoordinates (q : E3))).1)
    let Y : Set (ℝ × E2) := placed '' Qminus
    let H : E3 → ℝ × E2 := fun y =>
      ((heightPlaneCoordinates u y).2, (heightPlaneCoordinates u y).1)
    let Hinv : ℝ × E2 → E3 := fun p =>
      (heightPlaneCoordinates u).symm (p.2, p.1)
    let zflat : ℝ := c + kappa * (rho ^ 2 - lambda)
    let FlatParameter : Set (ℝ × E2) :=
      {zflat} ×ˢ closedBall (0 : E2) rFlat
    let flatMap : E2 → E3 := fun x =>
      A (Real.sqrt (rho ^ 2 - lambda) • x, zflat)
    let Flat : Set E3 := flatMap '' closedBall (0 : E2) rFlat
    Y ⊆ T.source ∧ Y ⊆ Q.source ∧
      (∀ q ∈ Qminus, ∃ qR ∈ Qminus,
        heightCoordinates (qR : E3) =
          (R (heightCoordinates (q : E3)).1, (heightCoordinates (q : E3)).2) ∧
        placed q ∈ T.source ∧
        (horizontal qR, c + kappa * distance qR) ∈ A.source ∧
        endpoint qR ∈ A.target ∧
        H (endpoint qR) = T (placed q) ∧
        T.symm (H (endpoint qR)) = placed q) ∧
      H '' cap = T '' Y ∧ T '' Y = Q '' Y ∧
      H '' cap ⊆ T.target ∧ H '' cap ⊆ Q.target ∧
      cap = Hinv '' (Q '' Y) ∧ Q.symm '' (H '' cap) = Y ∧
      FlatParameter ⊆ Y ∧ T '' FlatParameter = Q '' FlatParameter ∧
      Flat = Hinv '' (Q '' FlatParameter) ∧ Flat ⊆ cap ∧
      (∀ x ∈ closedBall (0 : E2) rFlat,
        (Real.sqrt (rho ^ 2 - lambda) • x, zflat) ∈ A.source ∧
        flatMap x ∈ A.target) := by
  classical
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let coord := fun q : UnitTwoSphere => heightCoordinates (q : E3)
  let Qminus := {q : UnitTwoSphere | (coord q).2 ≤ 0}
  let distance := fun q : UnitTwoSphere => rho ^ 2 + lambda * (M (coord q)).2
  let horizontal := fun q : UnitTwoSphere => Real.sqrt (distance q) • (M (coord q)).1
  let endpoint := fun q : UnitTwoSphere => A (horizontal q, c + kappa * distance q)
  let cap := endpoint '' Qminus
  let s := c + kappa * rho ^ 2
  let placed := fun q : UnitTwoSphere =>
    (s + kappa * lambda * (M (coord q)).2, (M (coord q)).1)
  let Y := placed '' Qminus
  let H := fun y : E3 =>
    ((heightPlaneCoordinates u y).2, (heightPlaneCoordinates u y).1)
  let Hinv := fun p : ℝ × E2 => (heightPlaneCoordinates u).symm (p.2, p.1)
  let zflat := c + kappa * (rho ^ 2 - lambda)
  let FlatParameter := {zflat} ×ˢ closedBall (0 : E2) rFlat
  let flatMap := fun x : E2 => A (Real.sqrt (rho ^ 2 - lambda) • x, zflat)
  let Flat := flatMap '' closedBall (0 : E2) rFlat
  obtain ⟨hYT, hYQ, himage⟩ := stackCanonicalCap_image_eq_of_annular_match
    T Q hT hTi hQ hQi hTh hQh s kappa lambda gamma delta hkappa hlambda hlg hdelta
      hTs hQs hmatch rFlat rOne v0 v1 hrFlat hrann hradii hrOne hv0 hv01 hv1 hgap
  change Y ⊆ T.source at hYT
  change Y ⊆ Q.source at hYQ
  change T '' Y = Q '' Y at himage
  have hksq : kappa ^ 2 = 1 := by
    rw [← sq_abs, hkappa, one_pow]
  have hplacedHeight (q : UnitTwoSphere) : (placed q).1 = c + kappa * distance q := by
    dsimp only [placed, s, distance]
    ring
  have hrad (q : UnitTwoSphere) : kappa * ((placed q).1 - c) = distance q := by
    rw [hplacedHeight]
    calc
      kappa * (c + kappa * distance q - c) = kappa ^ 2 * distance q := by ring
      _ = distance q := by rw [hksq, one_mul]
  have hflatRad : kappa * (zflat - c) = rho ^ 2 - lambda := by
    calc
      kappa * (zflat - c) = kappa ^ 2 * (rho ^ 2 - lambda) := by dsimp [zflat]; ring
      _ = rho ^ 2 - lambda := by rw [hksq, one_mul]
  have hflatPositive : 0 < rho ^ 2 - lambda := by
    linarith only [hsmall, sq_pos_of_pos hrho]
  have hM (p : E2 × ℝ) : M p = (a p.2 • p.1, b (a p.2 • p.1) * p.2) := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
  have hbR (S : E2 ≃ₗᵢ[ℝ] E2) (x : E2) : b (S x) = b x := by
    simp only [b, stackCanonicalVertical, S.norm_map]
  have hMR (S : E2 ≃ₗᵢ[ℝ] E2) (p : E2 × ℝ) :
      M (S p.1, p.2) = (S (M p).1, (M p).2) := by
    rw [hM, hM]
    simp only [← S.map_smul, hbR]
  let rot (S : E2 ≃ₗᵢ[ℝ] E2) (q : UnitTwoSphere) : UnitTwoSphere :=
    ⟨heightCoordinates.symm (S (coord q).1, (coord q).2), by
      apply mem_sphere_zero_iff_norm.mpr
      have hn := heightCoordinates_symm_norm_sq (S (coord q).1, (coord q).2)
      rw [S.norm_map] at hn
      have hq := sphere_height_coordinates_sq q
      change ‖(coord q).1‖ ^ 2 + (coord q).2 ^ 2 = 1 at hq
      nlinarith [norm_nonneg (heightCoordinates.symm (S (coord q).1, (coord q).2))]⟩
  have hrot (S : E2 ≃ₗᵢ[ℝ] E2) (q : UnitTwoSphere) :
      coord (rot S q) = (S (coord q).1, (coord q).2) :=
    heightCoordinates.apply_symm_apply _
  have hrotmem (S : E2 ≃ₗᵢ[ℝ] E2) (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      rot S q ∈ Qminus := by
    change (coord (rot S q)).2 ≤ 0
    rw [hrot]
    exact hq
  have hrotinv (q : UnitTwoSphere) : rot R (rot R.symm q) = q := by
    apply Subtype.ext
    apply heightCoordinates.injective
    change coord (rot R (rot R.symm q)) = coord q
    rw [hrot, hrot, R.apply_symm_apply]
  have hdrot (S : E2 ≃ₗᵢ[ℝ] E2) (q : UnitTwoSphere) :
      distance (rot S q) = distance q := by
    dsimp only [distance]
    rw [hrot, hMR]
  have hhrot (S : E2 ≃ₗᵢ[ℝ] E2) (q : UnitTwoSphere) :
      horizontal (rot S q) = Real.sqrt (distance q) • S (M (coord q)).1 := by
    dsimp only [horizontal]
    rw [hdrot, hrot, hMR]
  have hcoords (q : UnitTwoSphere) :
      (horizontal (rot R q), c + kappa * distance (rot R q)) =
        (Real.sqrt (kappa * ((placed q).1 - c)) • R (placed q).2, (placed q).1) := by
    apply Prod.ext
    · rw [hhrot, hrad]
    · rw [hdrot, hplacedHeight]
  have hpoint (q : UnitTwoSphere) : H (endpoint (rot R q)) = T (placed q) := by
    rw [hTform]
    change H (A (horizontal (rot R q), c + kappa * distance (rot R q))) =
      H (A (Real.sqrt (kappa * ((placed q).1 - c)) • R (placed q).2, (placed q).1))
    rw [hcoords]
  have hAsource (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      (horizontal (rot R q), c + kappa * distance (rot R q)) ∈ A.source := by
    have hp := hYT (mem_image_of_mem placed hq)
    rw [hTsource] at hp
    rw [hcoords]
    exact hp.2
  have hHcap : H '' cap = T '' Y := by
    apply Subset.antisymm
    · rintro y ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨placed (rot R.symm q), ⟨rot R.symm q, hrotmem R.symm q hq, rfl⟩, ?_⟩
      rw [← hpoint, hrotinv]
    · rintro y ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨endpoint (rot R q), ⟨rot R q, hrotmem R q hq, rfl⟩, hpoint q⟩
  have hHinvH (y : E3) : Hinv (H y) = y :=
    (heightPlaneCoordinates u).symm_apply_apply y
  have hinverseImage (K : Set E3) : Hinv '' (H '' K) = K := by
    rw [image_image]
    simp only [hHinvH, image_id']
  have hcap : cap = Hinv '' (Q '' Y) := by
    rw [← himage, ← hHcap, hinverseImage]
  have hQinverse : Q.symm '' (H '' cap) = Y := by
    rw [hHcap, himage]
    apply Subset.antisymm
    · rintro y ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      simpa only [Q.left_inv (hYQ hp)] using hp
    · intro p hp
      exact ⟨Q p, mem_image_of_mem Q hp, Q.left_inv (hYQ hp)⟩
  have hr1 : rFlat < 1 := hradii.trans hrOne
  have hgeom (q : UnitTwoSphere) (hq : q ∈ Qminus) :=
    stackCanonicalModel_southern_geometry rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1 hgap (coord q) (sphere_height_coordinates_sq q) hq
  have hband (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      (placed q).1 ∈ Icc (s - gamma) (s + gamma) := by
    have hg := hgeom q hq
    have hv : |(M (coord q)).2| ≤ 1 :=
      abs_le.mpr ⟨hg.2.2.1, hg.2.2.2.1.trans zero_le_one⟩
    have hh : |kappa * lambda * (M (coord q)).2| ≤ lambda := by
      rw [abs_mul, abs_mul, hkappa, abs_of_pos hlambda, one_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv hlambda.le
    have ht := abs_le.mp hh
    change s - gamma ≤ s + kappa * lambda * (M (coord q)).2 ∧
      s + kappa * lambda * (M (coord q)).2 ≤ s + gamma
    constructor <;> linarith only [ht.1, ht.2, hlg]
  have hflatY : FlatParameter ⊆ Y := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    have hz' : z = zflat := hz
    subst z
    have hxnorm := mem_closedBall_zero_iff.mp hx
    refine ⟨southSpherePoint x, ?_, ?_⟩
    · change (heightCoordinates (southSpherePoint x : E3)).2 ≤ 0
      rw [southSpherePoint_coordinates _ (hxnorm.trans_lt hr1)]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    · have hf := (stackCanonicalModel_flat_disc rFlat rOne v0 v1
        hrFlat hradii hrOne hv0 hv01 hv1 hgap).1 x hxnorm
      change M (coord (southSpherePoint x)) = (x, -1) at hf
      change (s + kappa * lambda * (M (coord (southSpherePoint x))).2,
        (M (coord (southSpherePoint x))).1) = _
      rw [hf]
      exact Prod.ext (by dsimp [s, zflat]; ring) rfl
  have hsmallFlat (p : ℝ × E2) (hp : p ∈ Y) (hn : ‖p.2‖ ≤ rFlat) :
      p ∈ FlatParameter := by
    obtain ⟨q, hq, rfl⟩ := hp
    have hf := (hgeom q hq).2.2.2.2.1 hn
    change M (coord q) = ((coord q).1, -1) at hf
    refine ⟨?_, mem_closedBall_zero_iff.mpr hn⟩
    change s + kappa * lambda * (M (coord q)).2 = zflat
    rw [hf]
    dsimp [s, zflat]
    ring
  have houtside (p : ℝ × E2) (hp : p ∈ Y) (hn : p ∉ FlatParameter) : T p = Q p := by
    have hr : rFlat < ‖p.2‖ := lt_of_not_ge (fun hh => hn (hsmallFlat p hp hh))
    obtain ⟨q, hq, rfl⟩ := hp
    apply hmatch _ (hband q hq)
    have hnorm := (hgeom q hq).2.1
    exact abs_lt.mpr ⟨by linarith only [hr, hrann],
      (sub_nonpos.mpr hnorm).trans_lt hdelta⟩
  have hflatTransfer (V W : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
      (hYV : Y ⊆ V.source) (hVW : V '' Y = W '' Y)
      (hagree : ∀ p ∈ Y, p ∉ FlatParameter → V p = W p) :
      V '' FlatParameter ⊆ W '' FlatParameter := by
    rintro y ⟨p, hp, rfl⟩
    have hy : V p ∈ W '' Y := hVW ▸ mem_image_of_mem V (hflatY hp)
    obtain ⟨q, hq, heq⟩ := hy
    by_cases hqf : q ∈ FlatParameter
    · exact ⟨q, hqf, heq⟩
    · exfalso
      apply hqf
      have he : q = p := V.injOn (hYV hq) (hYV (hflatY hp))
        ((hagree q hq hqf).trans heq)
      exact he.symm ▸ hp
  have hflatEqual : T '' FlatParameter = Q '' FlatParameter :=
    Subset.antisymm (hflatTransfer T Q hYT himage houtside)
      (hflatTransfer Q T hYQ himage.symm (fun p hp hn => (houtside p hp hn).symm))
  have hflatPoint (x : E2) : T (zflat, x) = H (flatMap (R x)) := by
    rw [hTform]
    change H (A (Real.sqrt (kappa * (zflat - c)) • R x, zflat)) = _
    rw [hflatRad]
  have hHflat : H '' Flat = T '' FlatParameter := by
    apply Subset.antisymm
    · rintro y ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨(zflat, R.symm x), ⟨rfl, ?_⟩, ?_⟩
      · apply mem_closedBall_zero_iff.mpr
        rw [R.symm.norm_map]
        exact mem_closedBall_zero_iff.mp hx
      · rw [hflatPoint, R.apply_symm_apply]
    · rintro y ⟨⟨z, x⟩, ⟨hz, hx⟩, rfl⟩
      have hz' : z = zflat := hz
      subst z
      refine ⟨flatMap (R x), ⟨R x, ?_, rfl⟩, (hflatPoint x).symm⟩
      apply mem_closedBall_zero_iff.mpr
      rw [R.norm_map]
      exact mem_closedBall_zero_iff.mp hx
  have hFlat : Flat = Hinv '' (Q '' FlatParameter) := by
    rw [← hflatEqual, ← hHflat, hinverseImage]
  have hFlatCap : Flat ⊆ cap := by
    rw [hFlat, hcap]
    exact image_mono (image_mono hflatY)
  have hflatSource (x : E2) (hx : x ∈ closedBall (0 : E2) rFlat) :
      (Real.sqrt (rho ^ 2 - lambda) • x, zflat) ∈ A.source := by
    have hp : (zflat, R.symm x) ∈ FlatParameter := by
      refine ⟨rfl, mem_closedBall_zero_iff.mpr ?_⟩
      rw [R.symm.norm_map]
      exact mem_closedBall_zero_iff.mp hx
    have ht := hYT (hflatY hp)
    rw [hTsource] at ht
    change 0 < kappa * (zflat - c) ∧
      (Real.sqrt (kappa * (zflat - c)) • R (R.symm x), zflat) ∈ A.source at ht
    simpa only [hflatRad, R.apply_symm_apply, hflatPositive, true_and] using ht
  refine ⟨hYT, hYQ, ?_, hHcap, himage, ?_, ?_, hcap, hQinverse,
    hflatY, hflatEqual, hFlat, hFlatCap, ?_⟩
  · intro q hq
    refine ⟨rot R q, hrotmem R q hq, hrot R q, hYT (mem_image_of_mem placed hq),
      hAsource q hq, A.map_source (hAsource q hq), hpoint q, ?_⟩
    change T.symm (H (endpoint (rot R q))) = placed q
    rw [hpoint]
    exact T.left_inv (hYT (mem_image_of_mem placed hq))
  · rw [hHcap]
    rintro y ⟨p, hp, rfl⟩
    exact T.map_source (hYT hp)
  · rw [hHcap, himage]
    rintro y ⟨p, hp, rfl⟩
    exact Q.map_source (hYQ hp)
  · intro x hx
    exact ⟨hflatSource x hx, A.map_source (hflatSource x hx)⟩

end PoincareConjecture.M25.Topology3D
