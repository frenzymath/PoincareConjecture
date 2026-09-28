import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem finite_negative_halfCube {r : ℝ} (hr : 0 < r) :
    ∃ K : SimplicialComplex ℝ V3, K.faces.Finite ∧
      K.space = closedBall (0 : V3) r ∩ {z | z 2 ≤ 0} := by
  classical
  let A : Fin 3 ⊕ Fin 3 → V3 →ᵃ[ℝ] ℝ := fun i =>
    (signedCubeCoordinate i).toAffineMap - AffineMap.const ℝ V3 r
  let ell : V3 →ᵃ[ℝ] ℝ := (LinearMap.proj (2 : Fin 3)).toAffineMap
  let H := insert ell (Finset.univ.image A)
  have hrep : closedBall (0 : V3) r ∩ {z | z 2 ≤ 0} =
      {x | ∀ a ∈ H, a x ≤ 0} := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩ a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hx2
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        change signedCubeCoordinate i x - r ≤ 0
        exact sub_nonpos.mpr ((signedCubeCoordinate_le_norm i x).trans
          (by simpa only [mem_closedBall, dist_zero_right] using hx))
    · intro hx
      refine ⟨?_, hx ell (Finset.mem_insert_self _ _)⟩
      rw [mem_closedBall, dist_zero_right]
      apply (pi_norm_le_iff_of_nonneg hr.le).mpr
      intro i
      have hp : x i - r ≤ 0 := hx (A (.inl i))
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨.inl i, by simp, rfl⟩))
      have hn : -(x i) - r ≤ 0 := hx (A (.inr i))
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨.inr i, by simp, rfl⟩))
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact ((isCompact_closedBall (0 : V3) r).inter_right
    (isClosed_le (continuous_apply 2) continuous_const)).exists_finite_triangulation_of_halfspaces H hrep

private theorem exists_endpoint_negative_cap
    (B : OpenPartialHomeomorph V3 V3) (hB : B ∈ piecewiseAffineGroupoid V3)
    {p : V3} (hp : p ∈ B.source) (hBp : B p = 0)
    {A U : Set V3} (hU : IsOpen U) (hpU : p ∈ U)
    (haxis : ∀ x ∈ B.source,
      x ∈ A ↔ B x 0 = 0 ∧ B x 1 = 0 ∧ 0 ≤ B x 2) :
    ∃ (r : ℝ) (K : SimplicialComplex ℝ V3) (N V : Set V3),
      0 < r ∧ K.faces.Finite ∧
      closedBall (0 : V3) r ⊆ B.target ∧
      K.space = B.symm '' (closedBall (0 : V3) r ∩ {z | z 2 ≤ 0}) ∧
      N = B.symm '' (ball (0 : V3) r ∩ {z | z 2 < 0}) ∧
      IsOpen N ∧ closure N ⊆ K.space ∧ K.space ⊆ B.source ∩ U ∧
      K.space ∩ A ⊆ {p} ∧ Disjoint N A ∧
      IsOpen V ∧ p ∈ V ∧ V ⊆ B.source ∩ U ∧
      (∀ x ∈ V, x ∈ N ↔ B x 2 < 0) := by
  classical
  have hzero : (0 : V3) ∈ B.target := hBp ▸ B.map_source hp
  obtain ⟨T, hT, h0T, hTB, hBT⟩ := ((mem_piecewiseAffineGroupoid_iff V3 B).mp hB).2 0 hzero
  have hB0 : B.symm (0 : V3) = p := by rw [← hBp, B.left_inv hp]
  have hO : IsOpen (interior T.space ∩ (B.target ∩ B.symm ⁻¹' U)) :=
    isOpen_interior.inter (B.symm.isOpen_inter_preimage hU)
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.mp hO 0
    ⟨h0T, hzero, by simpa only [mem_preimage, hB0] using hpU⟩
  let r := δ / 2
  have hr : 0 < r := half_pos hδ
  have hcO : closedBall (0 : V3) r ⊆ interior T.space ∩ (B.target ∩ B.symm ⁻¹' U) :=
    fun x hx => hδO ((closedBall_subset_ball (half_lt_self hδ)) hx)
  have hcB : closedBall (0 : V3) r ⊆ B.target := fun x hx => (hcO hx).2.1
  let C : Set V3 := closedBall 0 r ∩ {z | z 2 ≤ 0}
  let D : Set V3 := ball 0 r ∩ {z | z 2 < 0}
  obtain ⟨L, hL, hLs⟩ := finite_negative_halfCube hr
  have hPL : FinitePiecewiseAffineOn B.symm C := by
    change FinitePiecewiseAffineOn B.symm (closedBall 0 r ∩ {z | z 2 ≤ 0})
    rw [← hLs]
    exact (hBT.finitePiecewiseAffineOn hT).restrict L hL
      (fun x hx => interior_subset (hcO (hLs.subset hx).1).1)
  obtain ⟨K, hK, hKs⟩ := hPL.exists_finite_triangulation_image
  let N := B.symm '' D
  let V := B.source ∩ B ⁻¹' ball 0 r
  have hDopen : IsOpen D := isOpen_ball.inter (isOpen_lt (continuous_apply 2) continuous_const)
  have hDB : D ⊆ B.target := fun _ hx => hcB (ball_subset_closedBall hx.1)
  have hNopen : IsOpen N := B.isOpen_image_symm_of_subset_target hDopen hDB
  have hKcompact : IsCompact K.space := K.isCompact_space_of_finite hK
  have hNK : N ⊆ K.space := by
    rw [hKs]
    exact image_mono (fun x hx => ⟨ball_subset_closedBall hx.1, (show x 2 < 0 from hx.2).le⟩)
  have hKBU : K.space ⊆ B.source ∩ U := by
    rw [hKs]
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨B.map_target (hcB hz.1), (hcO hz.1).2.2⟩
  have hKA : K.space ∩ A ⊆ {p} := by
    rintro x ⟨hxK, hxA⟩
    obtain ⟨z, hz, rfl⟩ := hKs.subset hxK
    have hzB := hcB hz.1
    have hax := (haxis _ (B.map_target hzB)).mp hxA
    rw [B.right_inv hzB] at hax
    have hz0 : z = 0 := by
      funext i
      fin_cases i
      · exact hax.1
      · exact hax.2.1
      · exact le_antisymm hz.2 hax.2.2
    simp only [hz0, hB0, mem_singleton_iff]
  have hNA : Disjoint N A := by
    apply disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hxA
    have hax := (haxis _ (B.map_target (hDB hz))).mp hxA
    rw [B.right_inv (hDB hz)] at hax
    exact hz.2.not_ge hax.2.2
  have hVopen : IsOpen V := B.isOpen_inter_preimage isOpen_ball
  have hpV : p ∈ V := ⟨hp, by change B p ∈ ball 0 r; rw [hBp]; exact mem_ball_self hr⟩
  have hVBU : V ⊆ B.source ∩ U := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hh := (hcO (ball_subset_closedBall hx.2)).2.2
    simpa only [mem_preimage, B.left_inv hx.1] using hh
  refine ⟨r, K, N, V, hr, hK, hcB, hKs, rfl, hNopen,
    closure_minimal hNK hKcompact.isClosed, hKBU, hKA, hNA, hVopen, hpV, hVBU, ?_⟩
  intro x hx
  constructor
  · rintro ⟨z, hz, hzx⟩
    rw [← hzx, B.right_inv (hDB hz)]
    exact hz.2
  · intro hx2
    exact ⟨B x, ⟨hx.2, hx2⟩, B.left_inv hx.1⟩





theorem exists_arc_endpoint_cap_region
    (B : Fin 2 → OpenPartialHomeomorph V3 V3)
    (hB : ∀ i, B i ∈ piecewiseAffineGroupoid V3)
    (p : Fin 2 → V3) (hp : ∀ i, p i ∈ (B i).source)
    (hBp : ∀ i, B i (p i) = 0)
    (hdis : Pairwise (fun i j => Disjoint (B i).source (B j).source))
    (A : Set V3)
    (haxis : ∀ i x, x ∈ (B i).source →
      (x ∈ A ↔ B i x 0 = 0 ∧ B i x 1 = 0 ∧ 0 ≤ B i x 2))
    (U : Fin 2 → Set V3) (hU : ∀ i, IsOpen (U i)) (hpU : ∀ i, p i ∈ U i) :
    ∃ (R : Set V3) (r : Fin 2 → ℝ)
      (K : Fin 2 → SimplicialComplex ℝ V3) (N V : Fin 2 → Set V3),
      R = (⋃ i, N i)ᶜ ∧ IsClosed R ∧
      (∀ i, 0 < r i ∧ (K i).faces.Finite ∧
        closedBall (0 : V3) (r i) ⊆ (B i).target ∧
        (K i).space = (B i).symm ''
          (closedBall (0 : V3) (r i) ∩ {z | z 2 ≤ 0}) ∧
        N i = (B i).symm '' (ball (0 : V3) (r i) ∩ {z | z 2 < 0}) ∧
        IsOpen (N i) ∧ closure (N i) ⊆ (K i).space ∧
        (K i).space ⊆ (B i).source ∩ U i ∧ (K i).space ∩ A = {p i} ∧
        IsOpen (V i) ∧ p i ∈ V i ∧ V i ⊆ (B i).source ∩ U i ∧
        (∀ x ∈ V i, x ∈ R ↔ 0 ≤ B i x 2) ∧
        (∀ x ∈ V i, x ∈ frontier R ↔ B i x 2 = 0)) ∧
      A ⊆ R ∧ A ∩ frontier R = {p 0, p 1} ∧
      A \ {p 0, p 1} ⊆ interior R ∧
      A ⊆ (⋃ i, V i) ∪ interior R := by
  classical
  choose r K N V hr hK hcB hKs hNs hNopen hNK hKBU hKA hNA hVopen hpV hVBU hVN using
    fun i => exists_endpoint_negative_cap (B i) (hB i) (hp i) (hBp i) (hU i) (hpU i) (haxis i)
  let R := (⋃ i, N i)ᶜ
  have hRclosed : IsClosed R := (isOpen_iUnion hNopen).isClosed_compl
  have hNsource (i : Fin 2) : N i ⊆ (B i).source :=
    subset_closure.trans ((hNK i).trans ((hKBU i).trans inter_subset_left))
  have hhalf (i : Fin 2) (x : V3) (hx : x ∈ V i) : x ∈ R ↔ 0 ≤ B i x 2 := by
    constructor
    · intro hxR
      apply le_of_not_gt
      intro hn
      exact hxR (mem_iUnion.mpr ⟨i, (hVN i x hx).mpr hn⟩)
    · intro hx2 hxN
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxN
      by_cases hji : j = i
      · subst j
        exact ((hVN i x hx).mp hxj).not_ge hx2
      · exact disjoint_left.mp (hdis (Ne.symm hji)) (hVBU i hx).1 (hNsource j hxj)
  let ell : V3 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj (2 : Fin 3)).toContinuousAffineMap
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : V3 →ₗ[ℝ] ℝ => f (fun _ => 1)) hz
    change (1 : ℝ) = 0 at hh
    norm_num at hh
  have hfront (i : Fin 2) (x : V3) (hx : x ∈ V i) :
      x ∈ frontier R ↔ B i x 2 = 0 := by
    let Q := (B i).restrOpen (V i) (hVopen i)
    have hQhalf : ∀ y ∈ Q.source, y ∈ R ↔ 0 ≤ ell (Q y) :=
      fun y hy => hhalf i y hy.2
    have hh := Q.isImage_frontier_of_affine_nonneg ell hell hQhalf
    exact (hh.apply_mem_iff ⟨(hVBU i hx).1, hx⟩).symm
  have hpA (i : Fin 2) : p i ∈ A :=
    (haxis i (p i) (hp i)).mpr (by simp only [hBp, Pi.zero_apply, le_refl, and_self])
  have hpfront (i : Fin 2) : p i ∈ frontier R :=
    (hfront i (p i) (hpV i)).mpr (by rw [hBp]; rfl)
  have hAR : A ⊆ R := by
    intro x hx hxN
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxN
    exact disjoint_left.mp (hNA i) hi hx
  have hpfin (i : Fin 2) : p i ∈ ({p 0, p 1} : Set V3) := by
    fin_cases i <;> simp
  have haway : A \ {p 0, p 1} ⊆ interior R := by
    rintro x ⟨hxA, hxend⟩
    have hxout : x ∈ (⋃ i, (K i).space)ᶜ := by
      intro hxK
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxK
      have hxp : x = p i := hKA i ⟨hi, hxA⟩
      exact hxend (hxp.symm ▸ hpfin i)
    have hopen : IsOpen (⋃ i, (K i).space)ᶜ :=
      (isClosed_iUnion_of_finite (fun i => ((K i).isCompact_space_of_finite (hK i)).isClosed)).isOpen_compl
    apply interior_maximal (show (⋃ i, (K i).space)ᶜ ⊆ R from ?_) hopen hxout
    intro y hy hyn
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyn
    exact hy (mem_iUnion.mpr ⟨i, hNK i (subset_closure hi)⟩)
  have hAfront : A ∩ frontier R = {p 0, p 1} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hn
      exact disjoint_left.mp disjoint_interior_frontier (haway ⟨hx.1, hn⟩) hx.2
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨hpA 0, hpfront 0⟩
      · have hx' : x = p 1 := hx
        subst x
        exact ⟨hpA 1, hpfront 1⟩
  refine ⟨R, r, K, N, V, rfl, hRclosed, ?_, hAR, hAfront, haway, ?_⟩
  · intro i
    refine ⟨hr i, hK i, hcB i, hKs i, hNs i, hNopen i, hNK i, hKBU i,
      Subset.antisymm (hKA i) ?_, hVopen i, hpV i, hVBU i, hhalf i, hfront i⟩
    rintro x rfl
    refine ⟨?_, hpA i⟩
    rw [hKs i]
    refine ⟨0, ⟨mem_closedBall_self (hr i).le, by simp⟩, ?_⟩
    rw [← hBp i, (B i).left_inv (hp i)]
  · intro x hx
    by_cases he : x ∈ ({p 0, p 1} : Set V3)
    · apply Or.inl
      rcases he with rfl | he
      · exact mem_iUnion.mpr ⟨0, hpV 0⟩
      · have he' : x = p 1 := he
        subst x
        exact mem_iUnion.mpr ⟨1, hpV 1⟩
    · exact Or.inr (haway ⟨hx, he⟩)

end PoincareConjecture.M76
