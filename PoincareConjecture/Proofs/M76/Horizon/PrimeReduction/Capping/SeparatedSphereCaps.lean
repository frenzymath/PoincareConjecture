import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.LiftedSphereCone
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions









set_option autoImplicit false

open Set Geometry

namespace Geometry.SeparatedSphereCaps

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq ι]


def lift (x : E) : E × (ι → ℝ) := (x, 0)


def apex (i : ι) : E × (ι → ℝ) := (0, Pi.single i 1)


def cap (i : ι) (S : Set E) : Set (E × (ι → ℝ)) :=
  convexJoin ℝ {apex i} (lift '' S)


theorem mem_cap_iff (i : ι) (S : Set E) (z : E × (ι → ℝ)) :
    z ∈ cap i S ↔ ∃ x ∈ S, ∃ t ∈ Icc (0 : ℝ) 1,
      z = ((1 - t) • x, t • Pi.single i 1) := by
  rw [cap, mem_convexJoin]
  constructor
  · rintro ⟨p, hp, y, ⟨x, hx, rfl⟩, a, b, ha, hb, hab, he⟩
    have hp' : p = apex i := mem_singleton_iff.mp hp
    subst p
    refine ⟨x, hx, a, ⟨ha, by linarith⟩, ?_⟩
    have hb' : b = 1 - a := by linarith
    simpa [apex, lift, hb'] using he.symm
  · rintro ⟨x, hx, t, ht, rfl⟩
    refine ⟨apex i, mem_singleton _, lift x, mem_image_of_mem lift hx,
      t, 1 - t, ht.1, sub_nonneg.mpr ht.2, by ring, ?_⟩
    simp [apex, lift]


theorem cap_inter_lift (i : ι) {S R : Set E} (hSR : S ⊆ R) :
    cap i S ∩ lift '' R = lift '' S := by
  ext z
  constructor
  · rintro ⟨hc, y, hy, rfl⟩
    obtain ⟨x, hx, t, ht, he⟩ := (mem_cap_iff i S (lift y)).mp hc
    have ht0 : t = 0 := by
      have h := congrArg (fun w : E × (ι → ℝ) => w.2 i) he
      simpa [lift] using h.symm
    have hyx : y = x := by simpa [lift, ht0] using congrArg Prod.fst he
    exact ⟨x, hx, by rw [hyx]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨subset_convexJoin_right (singleton_nonempty _) (mem_image_of_mem lift hx),
      mem_image_of_mem lift (hSR hx)⟩


theorem disjoint_caps {i j : ι} (hij : i ≠ j) {S T : Set E}
    (hST : Disjoint S T) : Disjoint (cap i S) (cap j T) := by
  apply disjoint_left.mpr
  intro z hzS hzT
  obtain ⟨x, hx, a, ha, hza⟩ := (mem_cap_iff i S z).mp hzS
  obtain ⟨y, hy, b, hb, hzb⟩ := (mem_cap_iff j T z).mp hzT
  have he := hza.symm.trans hzb
  have ha0 : a = 0 := by
    simpa [Pi.single_apply, hij] using congrArg (fun w : E × (ι → ℝ) => w.2 i) he
  have hb0 : b = 0 := by
    simpa [Pi.single_apply, hij.symm] using
      (congrArg (fun w : E × (ι → ℝ) => w.2 j) he).symm
  have hxy : x = y := by simpa [ha0, hb0] using congrArg Prod.fst he
  exact disjoint_left.mp hST hx (hxy ▸ hy)

variable [FiniteDimensional ℝ E] [Fintype ι]



theorem isFinitePLBallPair_cap {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (i : ι) {S : Set E} {T : Set F} {e : S ≃ₜ frontier T}
    (he : e.IsFinitePL) (hne : S.Nonempty) (hT : IsCompact T)
    (hcv : Convex ℝ T) (hTi : (interior T).Nonempty) :
    IsFinitePLBallPair F (cap i S) (lift '' S) := by
  let b : E × ℝ →L[ℝ] E × (ι → ℝ) :=
    (ContinuousLinearMap.fst ℝ E ℝ).prod
      ((ContinuousLinearMap.snd ℝ E ℝ).smulRight (Pi.single i 1))
  have hbi : Function.Injective b := by
    intro x y h
    apply Prod.ext
    · simpa [b] using congrArg Prod.fst h
    · simpa [b] using congrArg (fun w : E × (ι → ℝ) => w.2 i) h
  have hbase : b '' ((fun x : E => (x, (0 : ℝ))) '' S) = lift '' S := by
    rw [image_image]
    apply image_congr
    intro x hx
    simp [b, lift]
  have hcone : b '' convexJoin ℝ {((0 : E), (1 : ℝ))}
      ((fun x : E => (x, (0 : ℝ))) '' S) = cap i S := by
    change (b.toContinuousAffineMap : E × ℝ →ᵃ[ℝ] E × (ι → ℝ)) '' _ = _
    rw [AffineMap.image_convexJoin, image_singleton]
    change convexJoin ℝ {b (0, 1)} (b '' ((fun x : E => (x, (0 : ℝ))) '' S)) = _
    rw [hbase]
    simp [b, cap, apex]
  have hball := (he.isFinitePLBallPair_lifted_sphere_cone hne hT hcv hTi).affine_image
    b.toContinuousAffineMap hbi.injOn
  change IsFinitePLBallPair F (b '' _) (b '' _) at hball
  rwa [hcone, hbase] at hball



theorem exists_finite_capped_complex {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (S : ι → Set E) (hSK : ∀ i, S i ⊆ K.space)
    (hdisj : Pairwise (fun i j => Disjoint (S i) (S j)))
    {T : Set F} (e : ∀ i, S i ≃ₜ frontier T)
    (he : ∀ i, (e i).IsFinitePL) (hne : ∀ i, (S i).Nonempty)
    (hT : IsCompact T) (hcv : Convex ℝ T) (hTi : (interior T).Nonempty) :
    (∀ i, IsFinitePLBallPair F (cap i (S i)) (lift '' S i)) ∧
    (∀ i, cap i (S i) ∩ lift '' K.space = lift '' S i) ∧
    Pairwise (fun i j => Disjoint (cap i (S i)) (cap j (S j))) ∧
    ∃ L : SimplicialComplex ℝ (E × (ι → ℝ)), L.faces.Finite ∧
      L.space = lift '' K.space ∪ ⋃ i, cap i (S i) := by
  classical
  have hball (i : ι) := isFinitePLBallPair_cap i (he i) (hne i) hT hcv hTi
  refine ⟨hball, fun i => cap_inter_lift i (hSK i),
    fun i j hij => disjoint_caps hij (hdisj hij), ?_⟩
  have htri (i : ι) : ∃ J : SimplicialComplex ℝ (E × (ι → ℝ)),
      J.faces.Finite ∧ J.space = cap i (S i) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ := hball i
    exact ⟨J, hJ, hJs⟩
  choose J hJ hJs using htri
  obtain ⟨Q, hQ, hQs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion J hJ
  let u : E →ᴬ[ℝ] E × (ι → ℝ) :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E 0)
  have hu : Function.Injective u := fun x y h => congrArg Prod.fst h
  let A := (K.affineOnFaces_affine u).embeddedImage hu.injOn
  have hA : A.faces.Finite := (K.affineOnFaces_affine u).embeddedImage_finite hu.injOn hK
  have hAs : A.space = lift '' K.space := by
    rw [SimplicialComplex.AffineOnFaces.embeddedImage_space]
    rfl
  obtain ⟨L, hL, hLs⟩ := A.exists_finite_triangulation_union Q hA hQ
  refine ⟨L, hL, hLs.trans ?_⟩
  rw [hAs, hQs]
  simp only [hJs]

end Geometry.SeparatedSphereCaps
