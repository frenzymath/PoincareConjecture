import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.CutMapOrientationTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PlanarBoundaryOrientation
import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningFaceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.GeometricCofaceSigns










set_option autoImplicit false

open Set Geometry Classical
open AbstractSimplicialComplex PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem affine_triangle_height_sign (ell : E →ᵃ[ℝ] ℝ) (a b c x : E)
    (ha : ell a = 0) (hb : ell b = 0)
    (hx : x ∈ convexHull ℝ ({a, b, c} : Set E)) (hne : ell x ≠ 0) :
    SignType.sign (ell x) = SignType.sign (ell c) := by
  have hvertices : ({a, b, c} : Set E) ⊆
      ell ⁻¹' Icc (min 0 (ell c)) (max 0 (ell c)) := by
    rintro y (rfl | rfl | rfl)
    · rw [mem_preimage, ha]; exact ⟨min_le_left _ _, le_max_left _ _⟩
    · rw [mem_preimage, hb]; exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hbound := convexHull_min hvertices ((convex_Icc _ _).affine_preimage ell) hx
  rcases lt_trichotomy (ell c) 0 with hneg | heq | hpos
  · have hxle : ell x ≤ 0 := by simpa [max_eq_left hneg.le] using hbound.2
    rw [sign_neg (lt_of_le_of_ne hxle hne), sign_neg hneg]
  · have hxzero : ell x = 0 := by simpa [heq] using hbound
    exact (hne hxzero).elim
  · have hxle : 0 ≤ ell x := by simpa [min_eq_left hpos.le] using hbound.1
    rw [sign_pos (lt_of_le_of_ne hxle (Ne.symm hne)), sign_pos hpos]



theorem affine_chart_edge_displacement (R : E →ᴬ[ℝ] (ℝ × ℝ))
    (a b x : E) (t : ℝ) (hx : x - a = t • (b - a)) :
    R x - R a = t • (R b - R a) := by
  have h := congrArg R.contLinear hx
  rw [map_smul] at h
  simpa only [← vsub_eq_sub, R.contLinear_map_vsub] using h



theorem refined_original_edge_cross_sign (R : E →ᴬ[ℝ] (ℝ × ℝ))
    (a b c x y z : E) (t u : ℝ)
    (hx : x - a = t • (b - a)) (hy : y - a = u • (b - a))
    (hz : z ∈ convexHull ℝ ({a, b, c} : Set E))
    (hne : planarCross (R y - R x) (R z - R x) ≠ 0) :
    SignType.sign (planarCross (R y - R x) (R z - R x)) =
      SignType.sign (u - t) * SignType.sign (planarCross (R b - R a) (R c - R a)) := by
  let ell : E →ᵃ[ℝ] ℝ := (planarCross (R b - R a)).toAffineMap.comp R.toAffineMap -
    AffineMap.const ℝ E (planarCross (R b - R a) (R a))
  have hvalue (w : E) : ell w = planarCross (R b - R a) (R w - R a) := by
    change planarCross (R b - R a) (R w) - planarCross (R b - R a) (R a) = _
    rw [map_sub]
  have ha : ell a = 0 := by rw [hvalue, sub_self, map_zero]
  have hb : ell b = 0 := by rw [hvalue, planarCross_self]
  have hRx := affine_chart_edge_displacement R a b x t hx
  have hRy := affine_chart_edge_displacement R a b y u hy
  have heq : planarCross (R y - R x) (R z - R x) = (u - t) * ell z := by
    rw [hvalue]
    have hx' : R x = t • (R b - R a) + R a := (sub_eq_iff_eq_add).mp hRx
    have hy' : R y = u • (R b - R a) + R a := (sub_eq_iff_eq_add).mp hRy
    rw [hx', hy']
    dsimp [planarCross]
    ring
  have hzn : ell z ≠ 0 := by intro he; apply hne; rw [heq, he, mul_zero]
  rw [heq, sign_mul, affine_triangle_height_sign ell a b c z ha hb hz hzn, hvalue]

theorem orientationSignParity_mul_nonzero (a b : SignType) (ha : a ≠ 0) (hb : b ≠ 0) :
    orientationSignParity (a * b) = orientationSignParity a + orientationSignParity b := by
  cases a <;> cases b <;> norm_num [orientationSignParity] at *
  decide

private theorem mapped_cross_parity_signed (d : ℝ) (hd : d ≠ 0) (i : Fin 3) :
    orientationSignParity (SignType.sign ((-1 : ℝ) ^ i.val * d)) =
      orientationSignParity (SignType.sign d) + (i.val : ZMod 2) := by
  rcases lt_or_gt_of_ne hd with h | h
  · have hn := sign_neg h
    have hp := sign_pos (neg_pos.mpr h)
    fin_cases i <;> norm_num [orientationSignParity, hn, hp]
    decide
  · have hp := sign_pos h
    have hn := sign_neg (neg_neg_of_pos h)
    fin_cases i <;> norm_num [orientationSignParity, hn, hp]

theorem mapped_numbered_boundary_cross_parity [DecidableEq E]
    (number : E → ℕ) (p : Fin 3 → E)
    (hp : Function.Injective p) (hnumber : StrictMono (number ∘ p))
    (f : E → ℝ × ℝ)
    (hd : planarCross (f (p 1) - f (p 0)) (f (p 2) - f (p 0)) ≠ 0) (i : Fin 3) :
    orientationSignParity (SignType.sign
      (planarCross (f (p (i.succAbove 1)) - f (p (i.succAbove 0)))
        (f (p i) - f (p (i.succAbove 0))))) =
      orientationSignParity (SignType.sign
        (planarCross (f (p 1) - f (p 0)) (f (p 2) - f (p 0)))) +
        Dehn.orderedCofaceParity number (Finset.univ.image p)
          (p (i.succAbove 0)) (p (i.succAbove 1)) := by
  have he : (Finset.univ.erase i).image p = {p (i.succAbove 0), p (i.succAbove 1)} := by
    ext x
    constructor
    · rintro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (Finset.mem_erase.mp hj).1
      fin_cases k <;> simp
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨i.succAbove 0,
          Finset.mem_erase.mpr ⟨Fin.succAbove_ne i 0, Finset.mem_univ _⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨i.succAbove 1,
          Finset.mem_erase.mpr ⟨Fin.succAbove_ne i 1, Finset.mem_univ _⟩, rfl⟩
  have hpar := boundaryFaceParity_ordered_triangle number p hp hnumber i
  rw [he] at hpar
  have hord : number (p (i.succAbove 0)) < number (p (i.succAbove 1)) :=
    hnumber ((Fin.strictMono_succAbove i) (by decide : (0 : Fin 2) < 1))
  have hcross := planar_triangle_boundary_cross (f ∘ p) i
  change planarCross (f (p (i.succAbove 1)) - f (p (i.succAbove 0)))
    (f (p i) - f (p (i.succAbove 0))) = _ at hcross
  simp only [Function.comp_apply] at hcross
  rw [hcross, mapped_cross_parity_signed _ hd i]
  simp only [Dehn.orderedCofaceParity, hpar, if_neg (not_lt_of_gt hord), add_zero]

private theorem mapped_numbered_boundary_cross_parity_reverse [DecidableEq E]
    (number : E → ℕ) (p : Fin 3 → E)
    (hp : Function.Injective p) (hnumber : StrictMono (number ∘ p))
    (f : E → ℝ × ℝ)
    (hd : planarCross (f (p 1) - f (p 0)) (f (p 2) - f (p 0)) ≠ 0) (i : Fin 3) :
    orientationSignParity (SignType.sign
      (planarCross (f (p (i.succAbove 0)) - f (p (i.succAbove 1)))
        (f (p i) - f (p (i.succAbove 1))))) =
      orientationSignParity (SignType.sign
        (planarCross (f (p 1) - f (p 0)) (f (p 2) - f (p 0)))) +
        Dehn.orderedCofaceParity number (Finset.univ.image p)
          (p (i.succAbove 1)) (p (i.succAbove 0)) := by
  have hbase := mapped_numbered_boundary_cross_parity number p hp hnumber f hd i
  have hcross : planarCross (f (p (i.succAbove 0)) - f (p (i.succAbove 1)))
      (f (p i) - f (p (i.succAbove 1))) =
      -planarCross (f (p (i.succAbove 1)) - f (p (i.succAbove 0)))
        (f (p i) - f (p (i.succAbove 0))) := by
    dsimp [planarCross]
    ring
  have hnonzero : planarCross (f (p (i.succAbove 1)) - f (p (i.succAbove 0)))
      (f (p i) - f (p (i.succAbove 0))) ≠ 0 := by
    change planarCross ((f ∘ p) (i.succAbove 1) - (f ∘ p) (i.succAbove 0))
      ((f ∘ p) i - (f ∘ p) (i.succAbove 0)) ≠ 0
    rw [planar_triangle_boundary_cross]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hd
  have hneg := mapped_cross_parity_signed _ hnonzero (1 : Fin 3)
  norm_num only [Fin.val_one, pow_one, neg_one_mul, Nat.cast_one] at hneg
  have hord : number (p (i.succAbove 0)) < number (p (i.succAbove 1)) :=
    hnumber ((Fin.strictMono_succAbove i) (by decide : (0 : Fin 2) < 1))
  have hrev := Dehn.orderedCofaceParity_reverse_of_label_ne number (Finset.univ.image p) hord.ne
  rw [hcross, hneg, hbase]
  linear_combination (norm := ring_nf) hrev
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, sub_zero]



theorem mapped_numbered_edge_apex_parity [DecidableEq E]
    (number : E → ℕ) (p : Fin 3 → E)
    (hp : Function.Injective p) (hnumber : StrictMono (number ∘ p))
    (f : E → ℝ × ℝ)
    (hd : planarCross (f (p 1) - f (p 0)) (f (p 2) - f (p 0)) ≠ 0)
    (a b x : E) (ha : a ∈ Finset.univ.image p) (hb : b ∈ Finset.univ.image p)
    (hx : x ∈ Finset.univ.image p) (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x) :
    orientationSignParity (SignType.sign (planarCross (f b - f a) (f x - f a))) =
      orientationSignParity (SignType.sign
        (planarCross (f (p 1) - f (p 0)) (f (p 2) - f (p 0)))) +
        Dehn.orderedCofaceParity number (Finset.univ.image p) a b := by
  obtain ⟨ia, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨ib, _, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨ix, _, rfl⟩ := Finset.mem_image.mp hx
  have hiab : ia ≠ ib := fun h ↦ hab (congrArg p h)
  have hiax : ia ≠ ix := fun h ↦ hax (congrArg p h)
  have hibx : ib ≠ ix := fun h ↦ hbx (congrArg p h)
  fin_cases ia <;> fin_cases ib <;> fin_cases ix
  all_goals first | exact (hiab rfl).elim | exact (hiax rfl).elim | exact (hibx rfl).elim | skip
  all_goals first
    | exact mapped_numbered_boundary_cross_parity number p hp hnumber f hd 0
    | exact mapped_numbered_boundary_cross_parity number p hp hnumber f hd 1
    | exact mapped_numbered_boundary_cross_parity number p hp hnumber f hd 2
    | exact mapped_numbered_boundary_cross_parity_reverse number p hp hnumber f hd 0
    | exact mapped_numbered_boundary_cross_parity_reverse number p hp hnumber f hd 1
    | exact mapped_numbered_boundary_cross_parity_reverse number p hp hnumber f hd 2




theorem exists_original_triangle_orientation_chart [FiniteDimensional ℝ E] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (number : E → ℕ) (hnumber : InjOn number K.vertices)
    {t : Finset E} (ht : t ∈ K.faces) (htc : t.card = 3) :
    ∃ R : E →ᴬ[ℝ] (ℝ × ℝ), InjOn R (convexHull ℝ (t : Set E)) ∧
      ∀ a ∈ t, ∀ b ∈ t, ∀ c ∈ t, a ≠ b → a ≠ c → b ≠ c →
        orientationSignParity (SignType.sign (planarCross (R b - R a) (R c - R a))) =
          Dehn.orderedCofaceParity number t a b := by
  have hv (x : t) : (x : E) ∈ K.vertices :=
    K.down_closed ht (Finset.singleton_subset_iff.mpr x.property) (by simp)
  let nt : t ↪ ℕ := ⟨fun x ↦ number x, fun x y h ↦
    Subtype.ext (hnumber (hv x) (hv y) h)⟩
  obtain ⟨q, hqi, hqimage, hqn⟩ := exists_numbered_triangle_enumeration
    nt Finset.univ (by simpa using htc)
  let p : Fin 3 → E := fun i ↦ q i
  have hpi : Function.Injective p := fun i j h ↦ hqi (Subtype.ext h)
  have hpt : Finset.univ.image p = t := by
    change Finset.univ.image (Subtype.val ∘ q) = t
    rw [Finset.image_comp, hqimage]
    ext x
    simp
  have hpn : StrictMono (number ∘ p) := hqn
  have hset : ({p 0, p 1, p 2} : Finset E) = t := by
    rw [← hpt]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> tauto
  obtain ⟨F, R, hRF, hFR, hF0, hF1, hF2, _⟩ :=
    K.exists_returning_face_coordinates (hpi.ne (by decide : (0 : Fin 3) ≠ 1))
      (hpi.ne (by decide : (0 : Fin 3) ≠ 2))
      (hpi.ne (by decide : (1 : Fin 3) ≠ 2)) (by
        convert ht using 1
        ext z
        simpa only [Finset.mem_insert, Finset.mem_singleton] using Finset.ext_iff.mp hset z)
  have hR0 : R (p 0) = (0, 0) := hF0 ▸ hRF (0, 0)
  have hR1 : R (p 1) = (1, 0) := hF1 ▸ hRF (1, 0)
  have hR2 : R (p 2) = (0, 1) := hF2 ▸ hRF (0, 1)
  have hRinv : EqOn (F ∘ R) id (convexHull ℝ (t : Set E)) := by
    intro x hx
    apply hFR
    apply convexHull_subset_affineSpan
    simpa only [← hset, Finset.coe_insert, Finset.coe_singleton] using hx
  have hdet : planarCross (R (p 1) - R (p 0)) (R (p 2) - R (p 0)) = 1 := by
    rw [hR0, hR1, hR2]
    norm_num [planarCross]
  refine ⟨R, fun x hx y hy he ↦ (hRinv hx).symm.trans ((congrArg F he).trans (hRinv hy)), ?_⟩
  intro a ha b hb c hc hab hac hbc
  have hpar := mapped_numbered_edge_apex_parity number p hpi hpn R
    (by rw [hdet]; norm_num) a b c (hpt.symm ▸ ha) (hpt.symm ▸ hb) (hpt.symm ▸ hc)
    hab hac hbc
  rw [hpt, hdet] at hpar
  simpa [orientationSignParity] using hpar



theorem exists_original_edge_parameters (a b x y : E)
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b) :
    ∃ t u : ℝ, x - a = t • (b - a) ∧ y - a = u • (b - a) := by
  rw [segment_eq_image_lineMap] at hx hy
  obtain ⟨t, _, rfl⟩ := hx
  obtain ⟨u, _, rfl⟩ := hy
  exact ⟨t, u, by simp [AffineMap.lineMap_apply_module'],
    by simp [AffineMap.lineMap_apply_module']⟩



theorem refined_original_cofaces_cancel [DecidableEq E]
    (number : E → ℕ) (T U : Finset E) (st su : ZMod 2)
    (R S : E →ᴬ[ℝ] (ℝ × ℝ)) (a b c d x y z w : E)
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hz : z ∈ convexHull ℝ ({a, b, c} : Set E))
    (hw : w ∈ convexHull ℝ ({a, b, d} : Set E))
    (hR : orientationSignParity (SignType.sign
      (planarCross (R b - R a) (R c - R a))) = Dehn.orderedCofaceParity number T a b)
    (hS : orientationSignParity (SignType.sign
      (planarCross (S b - S a) (S d - S a))) = Dehn.orderedCofaceParity number U a b)
    (hRn : planarCross (R y - R x) (R z - R x) ≠ 0)
    (hSn : planarCross (S y - S x) (S w - S x) ≠ 0)
    (hcancel : (st + boundaryFaceParity number T {a, b}) +
      (su + boundaryFaceParity number U {a, b}) = 1) :
    (st + orientationSignParity (SignType.sign (planarCross (R y - R x) (R z - R x)))) +
      (su + orientationSignParity (SignType.sign (planarCross (S y - S x) (S w - S x)))) = 1 := by
  obtain ⟨t, u, hxt, hyu⟩ := exists_original_edge_parameters a b x y hx hy
  have hsR := refined_original_edge_cross_sign R a b c x y z t u hxt hyu hz hRn
  have hsS := refined_original_edge_cross_sign S a b d x y w t u hxt hyu hw hSn
  have hnR : SignType.sign (u - t) *
      SignType.sign (planarCross (R b - R a) (R c - R a)) ≠ 0 := by
    rw [← hsR]
    exact sign_ne_zero.mpr hRn
  have hnS : SignType.sign (u - t) *
      SignType.sign (planarCross (S b - S a) (S d - S a)) ≠ 0 := by
    rw [← hsS]
    exact sign_ne_zero.mpr hSn
  rw [hsR, hsS, orientationSignParity_mul_nonzero _ _ (mul_ne_zero_iff.mp hnR).1
    (mul_ne_zero_iff.mp hnR).2, orientationSignParity_mul_nonzero _ _
      (mul_ne_zero_iff.mp hnS).1 (mul_ne_zero_iff.mp hnS).2, hR, hS]
  have hc := Dehn.orderedCofaceParity_cancellation number T U a b st su hcancel
  linear_combination (norm := ring_nf) hc
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, sub_zero]



theorem mapped_paired_edge_cross_product
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (f : (ℝ × ℝ) → ℝ × ℝ)
    (hf : L.AffineOnFaces f) (a b x y : ℝ × ℝ)
    (hab : a ≠ b) (hax : a ≠ x) (hay : a ≠ y)
    (hbx : b ≠ x) (hby : b ≠ y) (hxy : x ≠ y)
    (ht : {a, x, b} ∈ L.faces) (hu : {a, b, y} ∈ L.faces)
    (hi : InjOn f (convexHull ℝ ({a, x, b} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({a, b, y} : Set (ℝ × ℝ)))) :
    planarCross (f b - f a) (f x - f a) * planarCross (f b - f a) (f y - f a) < 0 := by
  let J : SimplicialComplex ℝ (ℝ × ℝ) :=
    { faces := {s | s ∈ L.faces ∧ (s ⊆ {a, x, b} ∨ s ⊆ {a, b, y})}
      indep := fun hs ↦ L.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        exact ⟨L.nonempty_of_mem_faces hs.1, fun t hts htne ↦
          ⟨L.down_closed hs.1 hts htne, hs.2.imp (hts.trans ·) (hts.trans ·)⟩⟩
      inter_subset_convexHull := fun hs ht ↦ L.inter_subset_convexHull hs.1 ht.1 }
  have hJsub : J.space ⊆ convexHull ℝ ({a, x, b} : Set (ℝ × ℝ)) ∪
      convexHull ℝ ({a, b, y} : Set (ℝ × ℝ)) := by
    intro z hz
    obtain ⟨s, hs, hzs⟩ := SimplicialComplex.mem_space_iff.mp hz
    exact hs.2.elim (fun h ↦ Or.inl (by
        simpa only [Finset.coe_insert, Finset.coe_singleton] using convexHull_mono h hzs))
      (fun h ↦ Or.inr (by
        simpa only [Finset.coe_insert, Finset.coe_singleton] using convexHull_mono h hzs))
  have hJf : J.AffineOnFaces f := fun s hs ↦ hf s hs.1
  have hJi : InjOn f J.space := hi.mono hJsub
  have htJ : {a, x, b} ∈ J.faces := ⟨ht, Or.inl Finset.Subset.rfl⟩
  have huJ : {a, b, y} ∈ J.faces := ⟨hu, Or.inr Finset.Subset.rfl⟩
  let M := hJf.embeddedImage hJi
  have htM : {f a, f x, f b} ∈ M.faces := by
    rw [hJf.embeddedImage_faces hJi]
    exact ⟨{a, x, b}, htJ, by simp⟩
  have huM : {f a, f b, f y} ∈ M.faces := by
    rw [hJf.embeddedImage_faces hJi]
    exact ⟨{a, b, y}, huJ, by simp⟩
  have haJ : a ∈ J.space := J.subset_space htJ (by simp)
  have hbJ : b ∈ J.space := J.subset_space htJ (by simp)
  have hxJ : x ∈ J.space := J.subset_space htJ (by simp)
  have hyJ : y ∈ J.space := J.subset_space huJ (by simp)
  exact planar_paired_edge_cross_product M (f a) (f b) (f x) (f y)
    (fun h ↦ hab (hJi haJ hbJ h)) (fun h ↦ hax (hJi haJ hxJ h))
    (fun h ↦ hay (hJi haJ hyJ h)) (fun h ↦ hbx (hJi hbJ hxJ h))
    (fun h ↦ hby (hJi hbJ hyJ h)) (fun h ↦ hxy (hJi hxJ hyJ h)) htM huM

end PoincareConjecture.M76.OriginalTriangleCopies
