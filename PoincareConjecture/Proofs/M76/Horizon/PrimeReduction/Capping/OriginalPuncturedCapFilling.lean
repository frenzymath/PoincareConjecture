import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PrescribedPuncturedBoundaryModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PhysicalPuncturedSphereCapFilling
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3ChangeRealization

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere

variable {X E F ι η : Type*} [TopologicalSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [Finite η]
  {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {R : Set X}

theorem HasPuncturedSphereModel.exists_prescribed_image_model
    (hm : HasPuncturedSphereModel e f R) (hR : IsClosed R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (P : η → Set X) (sP : ∀ j, ChartwisePLSphere e (P j))
    (hPdis : Pairwise fun j k => Disjoint (P j) (P k))
    (hfront : frontier R = ⋃ j, P j)
    (phi : X → F) (hphi : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphii : InjOn phi R) :
    ∃ (A r : η → Set V4)
      (C : (phi '' R) ≃ₜ (Sphere \ ⋃ j, A j \ r j : Set V4)),
      (∀ j, IsFinitePLBallPair V3 (A j) (r j) ∧ A j ⊆ Sphere ∧
        IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (A j \ r j))) ∧
      Pairwise (fun j k => Disjoint (A j) (A k)) ∧ C.IsFinitePL ∧
      (∀ j, phi '' P j ⊆ phi '' R) ∧
      ∀ j (x : phi '' R), (x : F) ∈ phi '' P j ↔ (C x : V4) ∈ r j := by
  obtain ⟨A, r, M, G, C, hA, hAdis, hG, hC, hPR, hmark, _⟩ :=
    hm.exists_prescribed_boundary_model hR K g hg hgi hreal P sP hPdis hfront
  have hgG (x : R) : g (G x) = (x : X) := by
    rw [hG]
    exact (hreal x x.property).2
  have hgM (y : M) : g y = (G.symm y : X) := by
    simpa only [G.apply_symm_apply] using hgG (G.symm y)
  have hMK : M ⊆ K.space := by
    intro y hy
    have h := (hreal (G.symm ⟨y, hy⟩) (G.symm ⟨y, hy⟩).property).1
    rwa [← hG, G.apply_symm_apply] at h
  have hgMR : MapsTo g M R := by
    intro y hy
    rw [hgM ⟨y, hy⟩]
    exact (G.symm ⟨y, hy⟩).property
  have hCcopy := hC
  obtain ⟨_, ⟨L, hL, hLM, _⟩, _⟩ := hCcopy
  have hcomp : FinitePiecewiseAffineOn (phi ∘ g) M := by
    rw [← hLM]
    exact (hg.restrict_finite L hL (hLM.subset.trans hMK)).finitePiecewiseAffineOn_comp
      L hL hphi
  have hcompi : InjOn (phi ∘ g) M := by
    intro x hx y hy hxy
    exact hgi (hMK hx) (hMK hy) (hphii (hgMR hx) (hgMR hy) hxy)
  obtain ⟨T, hT, hTval⟩ := hcomp.exists_homeomorph_image hcompi
  have himage : (phi ∘ g) '' M = phi '' R := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨g y, hgMR hy, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨G ⟨x, hx⟩, (G ⟨x, hx⟩).property, ?_⟩
      exact congrArg phi (hgG ⟨x, hx⟩)
  let J := (Homeomorph.setCongr (rfl : M = M)).trans
    (T.trans (Homeomorph.setCongr himage))
  have hJ : J.IsFinitePL := hT.setCongr rfl himage
  have hJval (y : M) : (J y : F) = phi (g y) := hTval y
  refine ⟨A, r, J.symm.trans C, hA, hAdis, hJ.symm.trans hC,
    (fun j => image_mono (hPR j)), ?_⟩
  intro j y
  obtain ⟨x, hx, hxy⟩ := y.property
  have hJy : J (G ⟨x, hx⟩) = y := by
    apply Subtype.ext
    rw [hJval, hgG]
    exact hxy
  rw [← hJy]
  change (J (G ⟨x, hx⟩) : F) ∈ phi '' P j ↔
    (C (J.symm (J (G ⟨x, hx⟩))) : V4) ∈ r j
  rw [J.symm_apply_apply, hJval, hgG]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have heq : z = x := hphii (hPR j hz) hx hzx
    exact (hmark j ⟨x, hx⟩).mp (heq ▸ hz)
  · intro hr
    exact ⟨x, (hmark j ⟨x, hx⟩).mpr hr, rfl⟩

theorem HasPuncturedSphereModel.isFinitePLBallPair_cap_filling_original_image
    (hm : HasPuncturedSphereModel e f R) (hR : IsClosed R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (P : η → Set X) (sP : ∀ j, ChartwisePLSphere e (P j))
    (hPdis : Pairwise fun j k => Disjoint (P j) (P k))
    (hfront : frontier R = ⋃ j, P j)
    (phi : X → F) (hphi : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphii : InjOn phi R) (i : η) (D : {j : η // j ≠ i} → Set F)
    (hD : ∀ j, IsFinitePLBallPair V3 (D j) (phi '' P j))
    (hcontact : ∀ j, D j ∩ phi '' R = phi '' P j)
    (hDdis : Pairwise fun j k => Disjoint (D j) (D k)) :
    IsFinitePLBallPair V3 (phi '' R ∪ ⋃ j, D j) (phi '' P i) := by
  obtain ⟨A, r, C, hA, hAdis, hC, hPR, hmark⟩ :=
    hm.exists_prescribed_image_model hR K g hg hgi hreal P sP hPdis hfront phi hphi hphii
  obtain ⟨_, _, _, _, hball⟩ := Set.exists_physical_punctured_sphere_cap_filling
    (phi '' R) A r (fun j => (hA j).1) (fun j => (hA j).2.1)
    (fun j => (hA j).2.2) hAdis i C hC (fun j => phi '' P j) hPR hmark D hD hcontact hDdis
  exact hball

theorem HasPuncturedSphereModel.exists_all_cap_filling_original_image
    (hm : HasPuncturedSphereModel e f R) (hR : IsClosed R)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ R, f x ∈ K.space ∧ g (f x) = x)
    (P : η → Set X) (sP : ∀ j, ChartwisePLSphere e (P j))
    (hPdis : Pairwise fun j k => Disjoint (P j) (P k))
    (hfront : frontier R = ⋃ j, P j)
    (phi : X → F) (hphi : ∀ i, LocallyPiecewiseAffineOn (phi ∘ (e i).symm) (e i).target)
    (hphii : InjOn phi R) (D : η → Set F)
    (hD : ∀ j, IsFinitePLBallPair V3 (D j) (phi '' P j))
    (hcontact : ∀ j, D j ∩ phi '' R = phi '' P j)
    (hDdis : Pairwise fun j k => Disjoint (D j) (D k)) :
    ∃ H : (phi '' R ∪ ⋃ j, D j : Set F) ≃ₜ Sphere, H.IsFinitePL := by
  obtain ⟨A, r, C, hA, hAdis, hC, hPR, hmark⟩ :=
    hm.exists_prescribed_image_model hR K g hg hgi hreal P sP hPdis hfront phi hphi hphii
  obtain ⟨H, hH, _, _⟩ := Set.exists_physical_punctured_sphere_all_cap_filling
    (phi '' R) A r (fun j => (hA j).1) (fun j => (hA j).2.1)
    (fun j => (hA j).2.2) hAdis C hC (fun j => phi '' P j) hPR hmark D hD hcontact hDdis
  exact ⟨H, hH⟩

end PoincareConjecture.M76
