import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.ControlledBoundaryHeight
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubpolyhedronZeroSet
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_controlled_finitePL_boundary_disk_push
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {D R : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D R)
    (K J : SimplicialComplex ℝ F) (hK : K.faces.Finite) (hJ : J.faces.Finite)
    (hJK : J.space ⊆ K.space) (C : E × ℝ → F)
    (hC : FinitePiecewiseAffineOn C (D ×ˢ Icc (0 : ℝ) 1))
    (hCi : InjOn C (D ×ˢ Icc (0 : ℝ) 1))
    (hCmap : MapsTo C (D ×ˢ Icc (0 : ℝ) 1) K.space)
    (hbase : ∀ x ∈ D, C (x, 0) ∈ J.space ↔ x ∈ R)
    {B : Set F} (hfront : ∀ z ∈ D ×ˢ Icc (0 : ℝ) 1, C z ∈ B ↔ z.2 = 0) :
    ∃ k : E → F, FinitePiecewiseAffineOn k D ∧ InjOn k D ∧
      MapsTo k D K.space ∧ EqOn k (fun x => C (x, 0)) R ∧
      IsFinitePLBallPair (ℝ × ℝ) (k '' D) ((fun x => C (x, 0)) '' R) ∧
      (k '' D) ∩ J.space = (fun x => C (x, 0)) '' R ∧
      (k '' D) ∩ B = (fun x => C (x, 0)) '' R := by
  obtain ⟨f, hf, hzero⟩ := K.exists_finitePL_subpolyhedron_zero_set J hK hJ hJK
    (show (0 : ℝ) < 1 by norm_num)
  have hFC : FinitePiecewiseAffineOn (f ∘ C) (D ×ˢ Icc (0 : ℝ) 1) :=
    hf.comp hC hCmap
  obtain ⟨h, hh, hhprop⟩ := exists_finitePL_disk_height_preserving_zero_set hD hFC
    (fun z hz => (hzero (C z) (hCmap hz)).1)
    (fun x hx => ((hzero (C (x, 0)) (hCmap ⟨hx, by simp⟩)).2).trans (hbase x hx))
  obtain ⟨L, _, hL, hLD, _, _⟩ := hD.exists_finite_carrier_and_rim_complexes
  have hid : FinitePiecewiseAffineOn (id : E → E) D :=
    ⟨L, hL, hLD, L.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)⟩
  let a : E → E × ℝ := fun x => (x, h x)
  have hamap : MapsTo a D (D ×ˢ Icc (0 : ℝ) 1) := fun x hx => ⟨hx, (hhprop x hx).1⟩
  let k := C ∘ a
  have hk : FinitePiecewiseAffineOn k D := hC.comp (hid.prod_mk hh) hamap
  have hki : InjOn k D := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hCi (hamap hx) (hamap hy) hxy)
  have hkr : EqOn k (fun x => C (x, 0)) R := by
    intro x hx
    change C (x, h x) = C (x, 0)
    rw [(hhprop x (hD.1 hx)).2.1.mpr hx]
  have hkj (x : E) (hx : x ∈ D) : k x ∈ J.space ↔ x ∈ R := by
    exact ((hzero (k x) (hCmap (hamap hx))).2).symm.trans (hhprop x hx).2.2
  have hkb (x : E) (hx : x ∈ D) : k x ∈ B ↔ x ∈ R :=
    (hfront (a x) (hamap hx)).trans (hhprop x hx).2.1
  have hball := hD.image hk hki
  rw [image_congr hkr] at hball
  refine ⟨k, hk, hki, hCmap.comp hamap, hkr, hball, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro y ⟨⟨x, hx, hxy⟩, hy⟩
      have hxr := (hkj x hx).mp (hxy.symm ▸ hy)
      exact ⟨x, hxr, (hkr hxr).symm.trans hxy⟩
    · rintro y ⟨x, hx, hxy⟩
      have hkxy := (hkr hx).trans hxy
      exact ⟨⟨x, hD.1 hx, hkxy⟩, hkxy ▸ (hkj x (hD.1 hx)).mpr hx⟩
  · apply Subset.antisymm
    · rintro y ⟨⟨x, hx, hxy⟩, hy⟩
      have hxr := (hkb x hx).mp (hxy.symm ▸ hy)
      exact ⟨x, hxr, (hkr hxr).symm.trans hxy⟩
    · rintro y ⟨x, hx, hxy⟩
      have hkxy := (hkr hx).trans hxy
      exact ⟨⟨x, hD.1 hx, hkxy⟩, hkxy ▸ (hkb x (hD.1 hx)).mpr hx⟩

end PoincareConjecture.M76
