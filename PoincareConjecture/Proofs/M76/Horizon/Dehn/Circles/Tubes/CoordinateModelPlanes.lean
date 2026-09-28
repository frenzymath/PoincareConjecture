import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.VertexCoordinateModel

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)


def coordinatePlaneIndex : Fin 3 → Fin 2 → Fin 3 := ![![1, 2], ![0, 2], ![0, 1]]

open Classical in


theorem finitePL_coordinate_model_planes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (W rim : Set E) (f : E → V3)
    (C0 : Set V3) (hC : IsCompact C0) (hcv : Convex ℝ C0)
    (hC0 : (0 : V3) ∈ interior C0) (L : (Fin 3 ⊕ Fin 3) → V3 →ₗ[ℝ] ℝ)
    (hrep : C0 = {x | ∀ j, L j x ≤ 1})
    (theta : W ≃ₜ C0) (htheta : theta.IsFinitePL)
    (hlink : ∀ z : W, (z : E) ∈ rim ↔ (theta z : V3) ∈ frontier C0)
    (hmarks : ∀ j (z : W), ((theta z : V3) j = 0 ↔ f z j = 0) ∧
      (0 ≤ (theta z : V3) j ↔ 0 ≤ f z j)) :
    ∀ (j : Fin 3) (active signs : Fin 2 → Bool),
      IsFinitePLBallPair P2
        {z | z ∈ W ∧ f z j = 0 ∧ ∀ k : Fin 2, active k = true →
          if signs k then 0 ≤ f z (coordinatePlaneIndex j k)
          else f z (coordinatePlaneIndex j k) ≤ 0}
        {z | z ∈ W ∧ f z j = 0 ∧
          (∀ k : Fin 2, active k = true →
            if signs k then 0 ≤ f z (coordinatePlaneIndex j k)
            else f z (coordinatePlaneIndex j k) ≤ 0) ∧
          (z ∈ rim ∨ ∃ k : Fin 2, active k = true ∧ f z (coordinatePlaneIndex j k) = 0)} := by
  classical
  obtain ⟨q, hq, hqval⟩ := htheta.symm
  have hqin (x : V3) (hx : x ∈ C0) : q x ∈ W := by
    rw [← hqval ⟨x, hx⟩]
    exact (theta.symm ⟨x, hx⟩).property
  have hforward (x : V3) (hx : x ∈ C0) : (theta ⟨q x, hqin x hx⟩ : V3) = x := by
    have he : (⟨q x, hqin x hx⟩ : W) = theta.symm ⟨x, hx⟩ :=
      Subtype.ext (hqval ⟨x, hx⟩).symm
    rw [he, theta.apply_symm_apply]
  have hback (z : W) : q (theta z) = z := by
    rw [← hqval (theta z), theta.symm_apply_apply]
  have hqi : InjOn q C0 := by
    intro x hx y hy he
    have he' : (⟨q x, hqin x hx⟩ : W) = ⟨q y, hqin y hy⟩ := Subtype.ext he
    have ht := congrArg (fun z : W => (theta z : V3)) he'
    exact (hforward x hx).symm.trans (ht.trans (hforward y hy))
  have hqzero (x : V3) (hx : x ∈ C0) (j : Fin 3) : x j = 0 ↔ f (q x) j = 0 := by
    have h := (hmarks j ⟨q x, hqin x hx⟩).1
    rwa [hforward x hx] at h
  have hqpos (x : V3) (hx : x ∈ C0) (j : Fin 3) : 0 ≤ x j ↔ 0 ≤ f (q x) j := by
    have h := (hmarks j ⟨q x, hqin x hx⟩).2
    rwa [hforward x hx] at h
  have hqside (x : V3) (hx : x ∈ C0) (j : Fin 3) (b : Bool) :
      (if b then 0 ≤ x j else x j ≤ 0) ↔
        (if b then 0 ≤ f (q x) j else f (q x) j ≤ 0) := by
    cases b
    · change x j ≤ 0 ↔ f (q x) j ≤ 0
      constructor
      · intro hn
        by_contra hp
        have hz := le_antisymm hn ((hqpos x hx j).mpr (le_of_lt (lt_of_not_ge hp)))
        exact (lt_of_not_ge hp).ne' ((hqzero x hx j).mp hz)
      · intro hn
        by_contra hp
        have hz := le_antisymm hn ((hqpos x hx j).mp (le_of_lt (lt_of_not_ge hp)))
        exact (lt_of_not_ge hp).ne' ((hqzero x hx j).mpr hz)
    · exact hqpos x hx j
  have hqfront (x : V3) (hx : x ∈ C0) : x ∈ frontier C0 ↔ q x ∈ rim := by
    rw [hlink ⟨q x, hqin x hx⟩, hforward x hx]
  have himage (P : V3 → Prop) (Q : E → Prop)
      (hPQ : ∀ x ∈ C0, P x ↔ Q (q x)) :
      q '' {x | x ∈ C0 ∧ P x} = {z | z ∈ W ∧ Q z} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hqin x hx.1, (hPQ x hx.1).mp hx.2⟩
    · rintro ⟨hz, hQ⟩
      refine ⟨theta ⟨z, hz⟩, ⟨(theta ⟨z, hz⟩).property, ?_⟩, hback ⟨z, hz⟩⟩
      apply (hPQ _ (theta ⟨z, hz⟩).property).mpr
      simpa only [hback] using hQ
  have hsection {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      [FiniteDimensional ℝ Y] {α : Type} [Fintype α]
      (a : Y →ᴬ[ℝ] V3) (r : V3 →ᴬ[ℝ] Y) (hleft : Function.LeftInverse r a)
      (ha0 : a 0 = 0) (cuts : α → Y →ₗ[ℝ] ℝ)
      (hpos : ∃ v : Y, ∀ i, 0 < cuts i v) :
      IsFinitePLBallPair Y {w | a w ∈ C0 ∧ ∀ i, 0 ≤ cuts i w}
        {w | (a w ∈ C0 ∧ ∀ i, 0 ≤ cuts i w) ∧
          (a w ∈ frontier C0 ∨ ∃ i, cuts i w = 0)} :=
    isFinitePLBallPair_convex_coordinate_section C0 hC hcv hC0 L hrep a r hleft ha0 cuts hpos
  let idx : Fin 3 → Fin 2 → Fin 3 := ![![1, 2], ![0, 2], ![0, 1]]
  have hidx0 (i : Fin 2) : idx i.castSucc 0 = i.rev.castSucc := by fin_cases i <;> rfl
  have hidx1 (i : Fin 2) : idx i.castSucc 1 = 2 := by fin_cases i <;> rfl
  let a (j : Fin 3) : P2 →ᴬ[ℝ] V3 := (ContinuousLinearMap.pi fun k : Fin 3 =>
    if k = idx j 0 then ContinuousLinearMap.fst ℝ ℝ ℝ else
      if k = idx j 1 then ContinuousLinearMap.snd ℝ ℝ ℝ else 0).toContinuousAffineMap
  let r (j : Fin 3) : V3 →ᴬ[ℝ] P2 :=
    ((ContinuousLinearMap.proj (idx j 0)).prod
      (ContinuousLinearMap.proj (idx j 1))).toContinuousAffineMap
  have hleft (j : Fin 3) : Function.LeftInverse (r j) (a j) := by
    intro w
    fin_cases j <;> simp [a, r, idx]
  have ha0 (j : Fin 3) : a j 0 = 0 := by fin_cases j <;> ext k <;> fin_cases k <;> simp [a, idx]
  have har (j : Fin 3) (x : V3) : a j (r j x) = x ↔ x j = 0 := by
    fin_cases j <;> simp [a, r, idx, funext_iff, Fin.forall_fin_succ, eq_comm]
  have hplane (j : Fin 3) (active signs : Fin 2 → Bool) :
      IsFinitePLBallPair P2
        {z | z ∈ W ∧ f z j = 0 ∧ ∀ k : Fin 2, active k = true →
          if signs k then 0 ≤ f z (idx j k) else f z (idx j k) ≤ 0}
        {z | z ∈ W ∧ f z j = 0 ∧
          (∀ k : Fin 2, active k = true →
            if signs k then 0 ≤ f z (idx j k) else f z (idx j k) ≤ 0) ∧
          (z ∈ rim ∨ ∃ k : Fin 2, active k = true ∧ f z (idx j k) = 0)} := by
    let cuts : {k : Fin 2 // active k = true} → P2 →ₗ[ℝ] ℝ := fun k =>
      (if signs k then 1 else -1 : ℝ) •
        (if (k : Fin 2) = 0 then LinearMap.fst ℝ ℝ ℝ else LinearMap.snd ℝ ℝ ℝ)
    have hpos : ∃ v : P2, ∀ k, 0 < cuts k v := by
      refine ⟨(if signs 0 then 1 else -1, if signs 1 then 1 else -1), ?_⟩
      rintro ⟨k, hk⟩
      fin_cases k
      · cases hs : signs 0 <;> norm_num [cuts, hs]
      · cases hs : signs 1 <;> norm_num [cuts, hs]
    have hside (x : V3) : (∀ k, 0 ≤ cuts k (r j x)) ↔
        ∀ k : Fin 2, active k = true →
          if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0 := by
      simp only [Subtype.forall]
      apply forall_congr'
      intro k
      apply forall_congr'
      intro hk
      fin_cases k
      · cases hs : signs 0 <;> simp [cuts, r, hs]
      · cases hs : signs 1 <;> simp [cuts, r, hs]
    have hzero (x : V3) : (∃ k, cuts k (r j x) = 0) ↔
        ∃ k : Fin 2, active k = true ∧ x (idx j k) = 0 := by
      constructor
      · rintro ⟨⟨k, hk⟩, hz⟩
        refine ⟨k, hk, ?_⟩
        fin_cases k
        · cases hs : signs 0 <;> simpa [cuts, r, hs] using hz
        · cases hs : signs 1 <;> simpa [cuts, r, hs] using hz
      · rintro ⟨k, hk, hz⟩
        refine ⟨⟨k, hk⟩, ?_⟩
        fin_cases k
        · cases hs : signs 0 <;> simpa [cuts, r, hs] using hz
        · cases hs : signs 1 <;> simpa [cuts, r, hs] using hz
    let U : Set P2 := {w | a j w ∈ C0 ∧ ∀ k, 0 ≤ cuts k w}
    let bU : Set P2 := {w | w ∈ U ∧ (a j w ∈ frontier C0 ∨ ∃ k, cuts k w = 0)}
    have huBall : IsFinitePLBallPair P2 U bU := hsection (a j) (r j) (hleft j) (ha0 j) cuts hpos
    have hUimage : a j '' U = {x | x ∈ C0 ∧ x j = 0 ∧ ∀ k : Fin 2,
        active k = true → if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0} := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨hw.1, (har j _).mp (by rw [hleft j]), ?_⟩
        apply (hside _).mp
        rw [hleft j w]
        exact hw.2
      · rintro ⟨hx, hz, hs⟩
        refine ⟨r j x, ⟨?_, (hside x).mpr hs⟩, (har j x).mpr hz⟩
        rwa [(har j x).mpr hz]
    have hbUimage : a j '' bU = {x | x ∈ C0 ∧ x j = 0 ∧
        (∀ k : Fin 2, active k = true →
          if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0) ∧
        (x ∈ frontier C0 ∨ ∃ k : Fin 2, active k = true ∧ x (idx j k) = 0)} := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        have h := hUimage.subset (mem_image_of_mem (a j) hw.1)
        refine ⟨h.1, h.2.1, h.2.2, ?_⟩
        rcases hw.2 with hc | hc
        · exact Or.inl hc
        · right
          apply (hzero _).mp
          rw [hleft j w]
          exact hc
      · rintro ⟨hx, hz, hs, hb⟩
        refine ⟨r j x, ⟨⟨?_, (hside x).mpr hs⟩, ?_⟩, (har j x).mpr hz⟩
        · rwa [(har j x).mpr hz]
        · rw [(har j x).mpr hz]
          exact hb.imp id (hzero x).mpr
    have hb := (huBall.affine_image (a j) (hleft j).injective.injOn).image_of_subset hq
      (by rintro _ ⟨w, hw, rfl⟩; exact hw.1) hqi
    rw [hUimage, hbUimage] at hb
    have hbdy := himage
      (fun x => x j = 0 ∧ ∀ k : Fin 2, active k = true →
        if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0)
      (fun z => f z j = 0 ∧ ∀ k : Fin 2, active k = true →
        if signs k then 0 ≤ f z (idx j k) else f z (idx j k) ≤ 0)
      (fun x hx => (hqzero x hx j).and (forall_congr' fun k =>
        forall_congr' fun (_ : active k = true) => hqside x hx (idx j k) (signs k)))
    have hrim := himage
      (fun x => x j = 0 ∧ (∀ k : Fin 2, active k = true →
        if signs k then 0 ≤ x (idx j k) else x (idx j k) ≤ 0) ∧
        (x ∈ frontier C0 ∨ ∃ k : Fin 2, active k = true ∧ x (idx j k) = 0))
      (fun z => f z j = 0 ∧ (∀ k : Fin 2, active k = true →
        if signs k then 0 ≤ f z (idx j k) else f z (idx j k) ≤ 0) ∧
        (z ∈ rim ∨ ∃ k : Fin 2, active k = true ∧ f z (idx j k) = 0))
      (fun x hx => (hqzero x hx j).and
        ((forall_congr' fun k => forall_congr' fun (_ : active k = true) =>
          hqside x hx (idx j k) (signs k)).and
          ((hqfront x hx).or (exists_congr fun k =>
            and_congr_right' (hqzero x hx (idx j k))))))
    simpa only [hbdy, hrim] using hb

  exact hplane

end PoincareConjecture.M76.Dehn

