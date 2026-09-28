import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.LocalDiskVertexCrossing
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

open Set Filter Geometry
open scoped Topology

namespace Geometry.SimplicialComplex

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

private theorem exists_centered_affine_height_coordinates
    (A : V3 →ᵃ[ℝ] ℝ) {p a : V3} (hp : A p = 0) (ha : 0 < A a) :
    ∃ F : C3 ≃ᴬ[ℝ] V3, F 0 = p ∧ ∀ z, A (F z) = z.2 := by
  let ell := A.linear
  let d : V3 := (A a)⁻¹ • (a - p)
  have hd : ell d = 1 := by
    change A.linear ((A a)⁻¹ • (a - p)) = 1
    have hsub : A.linear (a - p) = A a - A p := A.linearMap_vsub a p
    rw [map_smul, hsub, hp, sub_zero]
    exact inv_mul_cancel₀ ha.ne'
  have hell : ell ≠ 0 := by
    intro h
    have hzero : ell d = 0 := by rw [h]; rfl
    linarith
  have hker : Module.finrank ℝ ell.ker = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hell
    have hdim : Module.finrank ℝ V3 = 3 := by simp
    omega
  let e : V2 ≃ₗ[ℝ] ell.ker := LinearEquiv.ofFinrankEq _ _ (by
    simp [Module.finrank_prod, hker])
  let L : C3 →ₗ[ℝ] V3 :=
    (ell.ker.subtype.comp e.toLinearMap).comp (LinearMap.fst ℝ V2 ℝ) +
      (LinearMap.snd ℝ V2 ℝ).smulRight d
  have hL (z : C3) : L z = (e z.1 : V3) + z.2 • d := rfl
  have hheight (z : C3) : ell (L z) = z.2 := by
    have he0 : ell (e z.1 : V3) = 0 := (e z.1).property
    rw [hL, map_add, map_smul, he0, hd]
    simp
  have hi : Function.Injective L := by
    intro x y hxy
    have hlast : x.2 = y.2 := (hheight x).symm.trans ((congrArg ell hxy).trans (hheight y))
    have hfirst : (e x.1 : V3) = e y.1 := by
      have heq : (e x.1 : V3) + y.2 • d = (e y.1 : V3) + y.2 • d := by
        simpa only [hL, hlast] using hxy
      exact add_right_cancel heq
    exact Prod.ext (e.injective (Subtype.ext hfirst)) hlast
  have hsurj : Function.Surjective L := by
    intro x
    let y : ell.ker := ⟨x - ell x • d, by
      change ell (x - ell x • d) = 0
      rw [map_sub, map_smul, hd]
      simp⟩
    refine ⟨(e.symm y, ell x), ?_⟩
    rw [hL, e.apply_symm_apply]
    change x - ell x • d + ell x • d = x
    abel
  let B := (LinearEquiv.ofBijective L ⟨hi, hsurj⟩).toContinuousLinearEquiv
  let F := B.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ V3 p)
  have hF (z : C3) : F z = L z + p := add_comm _ _
  refine ⟨F, by rw [hF, map_zero, zero_add], ?_⟩
  intro z
  rw [hF]
  change A (L z +ᵥ p) = z.2
  rw [A.map_vadd, hp]
  exact (add_zero _).trans (hheight z)

theorem exists_affine_vertex_crossing_chart_of_local_disk
    (K L : SimplicialComplex ℝ V3) (hK : K.faces.Finite) (hLK : L ≤ K)
    (hbound : ∀ a ∈ L.faces, a.card ≤ 3)
    {p : V3} (hp : p ∈ L.vertices) (hint : p ∈ interior K.space)
    {d rim : Set V3} (hd : IsFinitePLBallPair (Fin 2 → ℝ) d rim)
    (hdL : d ⊆ L.space) (hpd : p ∈ d \ rim)
    (hopen : IsOpen ((Subtype.val : L.space → V3) ⁻¹' (d \ rim)))
    (A : V3 →ᵃ[ℝ] ℝ) {u v : V3} (hu : u ≠ p) (hv : v ≠ p)
    (hinter : segment ℝ p u ∩ segment ℝ p v ⊆ {p})
    (hlocal : ∀ᶠ x in 𝓝 p,
      x ∈ L.space ∩ {x | A x = 0} ↔ x ∈ segment ℝ p u ∪ segment ℝ p v)
    (hneg : p ∈ closure (L.space ∩ {x | A x < 0}))
    (hpos : p ∈ closure (L.space ∩ {x | 0 < A x}))
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ x ∈ H.source, x ∈ L.space ↔ (H x).2 = 0) ∧
      (∀ x ∈ H.source, A x = 0 ↔ (H x).1.1 = 0) ∧
      ∀ x ∈ H.source, 0 ≤ A x ↔ 0 ≤ (H x).1.1 := by
  classical
  have hpzero : A p = 0 :=
    ((mem_of_mem_nhds hlocal).mpr (Or.inl (left_mem_segment ℝ p u))).2
  obtain ⟨a, _, _, ha⟩ := mem_closure_iff.mp hpos univ isOpen_univ (mem_univ p)
  obtain ⟨F, hFzero, hFheight⟩ := exists_centered_affine_height_coordinates A hpzero ha
  have hFp : F.symm p = 0 := by rw [← hFzero, F.symm_apply_apply]
  have hheight (x : V3) : A x = (F.symm x).2 := by
    simpa only [F.apply_symm_apply] using hFheight (F.symm x)
  let hKF := K.affineOnFaces_affine F.symm.toContinuousAffineMap
  let hLF := L.affineOnFaces_affine F.symm.toContinuousAffineMap
  let K' := hKF.embeddedImage F.symm.injective.injOn
  let L' := hLF.embeddedImage F.symm.injective.injOn
  have hKs : K'.space = F.symm '' K.space := hKF.embeddedImage_space _
  have hLs : L'.space = F.symm '' L.space := hLF.embeddedImage_space _
  have hKfaces : K'.faces = (fun s : Finset V3 => s.image F.symm) '' K.faces :=
    hKF.embeddedImage_faces _
  have hLfaces : L'.faces = (fun s : Finset V3 => s.image F.symm) '' L.faces :=
    hLF.embeddedImage_faces _
  have hLmem (x : C3) : x ∈ L'.space ↔ F x ∈ L.space := by
    rw [hLs]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [F.apply_symm_apply] using hy
    · intro hx
      exact ⟨F x, hx, F.symm_apply_apply x⟩
  have hLK' : L' ≤ K' := by
    intro t ht
    change t ∈ L'.faces at ht
    change t ∈ K'.faces
    rw [hLfaces] at ht
    rw [hKfaces]
    obtain ⟨s, hs, rfl⟩ := ht
    exact ⟨s, hLK hs, rfl⟩
  have hbound' (t : Finset C3) (ht : t ∈ L'.faces) : t.card ≤ 3 := by
    rw [hLfaces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    exact Finset.card_image_le.trans (hbound s hs)
  have hp' : (0 : C3) ∈ L'.vertices := by
    have hverts : L'.vertices = F.symm '' L.vertices := hLF.embeddedImage_vertices _
    rw [hverts]
    exact ⟨p, hp, hFp⟩
  have hint' : (0 : C3) ∈ interior K'.space := by
    have hi : F.symm '' interior K.space = interior (F.symm '' K.space) :=
      F.symm.toHomeomorph.image_interior K.space
    rw [hKs, ← hi]
    exact ⟨p, hint, hFp⟩
  have hmem (S : Set V3) (x : C3) : x ∈ F.symm '' S ↔ F x ∈ S := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [F.apply_symm_apply] using hy
    · intro hx
      exact ⟨F x, hx, F.symm_apply_apply x⟩
  have hd' := hd.affine_image F.symm.toContinuousAffineMap F.symm.injective.injOn
  have hdL' : F.symm '' d ⊆ L'.space := by rw [hLs]; exact image_mono hdL
  have hpd' : (0 : C3) ∈ F.symm '' d \ F.symm '' rim := by
    rw [Set.mem_sdiff, hmem, hmem, hFzero]
    exact hpd
  let back : L'.space → L.space := fun y => ⟨F y, (hLmem y).mp y.property⟩
  have hbackcont : Continuous back :=
    (F.continuous.comp continuous_subtype_val).subtype_mk _
  have hopen' : IsOpen ((Subtype.val : L'.space → C3) ⁻¹'
      (F.symm '' d \ F.symm '' rim)) := by
    have heq : (Subtype.val : L'.space → C3) ⁻¹' (F.symm '' d \ F.symm '' rim) =
        back ⁻¹' ((Subtype.val : L.space → V3) ⁻¹' (d \ rim)) := by
      ext y
      change ((y : C3) ∈ F.symm '' d ∧ (y : C3) ∉ F.symm '' rim) ↔
        (F y ∈ d ∧ F y ∉ rim)
      rw [hmem, hmem]
    rw [heq]
    exact hopen.preimage hbackcont
  have hseg (w : V3) : F.symm '' segment ℝ p w = segment ℝ 0 (F.symm w) := by
    have h : F.symm '' segment ℝ p w = segment ℝ (F.symm p) (F.symm w) :=
      image_segment ℝ F.symm.toAffineEquiv.toAffineMap p w
    rw [h, hFp]
  have hsegmem (w : V3) (x : C3) :
      x ∈ segment ℝ 0 (F.symm w) ↔ F x ∈ segment ℝ p w := by
    rw [← hseg, hmem]
  have hu' : F.symm u ≠ 0 := fun h => hu (F.symm.injective (h.trans hFp.symm))
  have hv' : F.symm v ≠ 0 := fun h => hv (F.symm.injective (h.trans hFp.symm))
  have hinter' : segment ℝ 0 (F.symm u) ∩ segment ℝ 0 (F.symm v) ⊆ {0} := by
    intro x hx
    have he := hinter ⟨(hsegmem u x).mp hx.1, (hsegmem v x).mp hx.2⟩
    have hx : F x = p := he
    change x = 0
    simpa only [F.symm_apply_apply, hFp] using congrArg F.symm hx
  have hlocal' : ∀ᶠ x in 𝓝 (0 : C3),
      x ∈ L'.space ∩ {x | x.2 = 0} ↔
        x ∈ segment ℝ 0 (F.symm u) ∪ segment ℝ 0 (F.symm v) := by
    have ht : Tendsto F (𝓝 0) (𝓝 p) := hFzero ▸ F.continuous.tendsto 0
    filter_upwards [ht.eventually hlocal] with x hx
    simpa only [mem_inter_iff, mem_ofPred_eq, mem_union, hLmem, hsegmem, hFheight] using hx
  have hsign (q : ℝ → Prop) (hq : p ∈ closure (L.space ∩ {x | q (A x)})) :
      (0 : C3) ∈ closure (L'.space ∩ {x | q x.2}) := by
    have heq : F.symm '' (L.space ∩ {x | q (A x)}) = L'.space ∩ {x | q x.2} := by
      ext x
      rw [hmem, mem_inter_iff, mem_inter_iff, hLmem]
      simp only [mem_ofPred_eq, hFheight]
    have hc : F.symm '' closure (L.space ∩ {x | q (A x)}) =
        closure (F.symm '' (L.space ∩ {x | q (A x)})) :=
      F.symm.toHomeomorph.image_closure _
    rw [← heq, ← hc]
    exact ⟨p, hq, hFp⟩
  obtain ⟨T, hTzero, hTO, hT0, hTPL, hTwhole, hTzeroheight, hTpos⟩ :=
    K'.exists_vertex_crossing_chart_of_local_disk L' (hKF.embeddedImage_finite _ hK)
      hLK' hbound' hp' hint' hd' hdL' hpd' hopen' hu' hv' hinter' hlocal'
      (hsign (fun t => t < 0) hneg) (hsign (fun t => 0 < t) hpos)
      (hO.preimage F.continuous) (by simpa only [mem_preimage, hFzero] using hpO)
  let H := F.symm.toHomeomorph.toOpenPartialHomeomorph.trans T
  have hsource (x : V3) : x ∈ H.source ↔ F.symm x ∈ T.source := by
    change x ∈ univ ∩ F.symm ⁻¹' T.source ↔ _
    exact and_iff_right (mem_univ x)
  have hPL : LocallyPiecewiseAffineOn T T.source ∧
      LocallyPiecewiseAffineOn T.symm T.target := hTPL
  refine ⟨H, (hsource p).mpr (hFp.symm ▸ hTzero), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := hTO ((hsource x).mp hx)
    simpa only [mem_preimage, F.apply_symm_apply] using h
  · change T (F.symm p) = 0
    rw [hFp, hT0]
  · exact hPL.1.comp
      (locallyPiecewiseAffineOn_affine F.symm.toContinuousAffineMap isOpen_univ)
  · exact ((locallyPiecewiseAffineOn_affine F.toContinuousAffineMap isOpen_univ).comp
      hPL.2).mono H.open_target (fun _ hx => ⟨hx.1, mem_univ _⟩)
  · intro x hx
    change x ∈ L.space ↔ (T (F.symm x)).2 = 0
    have h := hTwhole (F.symm x) ((hsource x).mp hx)
    simpa only [hLmem, F.apply_symm_apply] using h
  · intro x hx
    exact (hheight x ▸ hTzeroheight (F.symm x) ((hsource x).mp hx))
  · intro x hx
    exact (hheight x ▸ hTpos (F.symm x) ((hsource x).mp hx))

end Geometry.SimplicialComplex
