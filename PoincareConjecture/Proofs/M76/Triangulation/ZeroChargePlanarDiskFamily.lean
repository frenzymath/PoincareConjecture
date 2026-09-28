import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDisk
import PoincareConjecture.Proofs.M76.Mathlib.PlanarDiskConvexContainment












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_planar_disk_of_whole_level_polygon
    (hdim : Module.finrank ℝ E = 3) (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    {S : Set E} {c : ℝ} {n : ℕ} (P : Polygon E (n + 3))
    (hP : P.HasSimplicialEdges) (hPinj : Function.Injective P)
    (hsection : P.boundary ℝ = S ∩ {x | A x = c}) :
    ∃ d : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = c}) ∧
      d ⊆ {x | A x = c} ∧ d ∩ S = S ∩ {x | A x = c} ∧
      ∀ C : Set E, Convex ℝ C → S ⊆ C → d ⊆ C := by
  let B := A - AffineMap.const ℝ E c
  have hB : B.linear ≠ 0 := by simpa [B] using hA
  obtain ⟨a, r, hleft, hright, ha⟩ := B.exists_zeroLevel_coordinates hB
    (F := ℝ × ℝ) (by simp [hdim, Module.finrank_prod])
  have hboundaryplane : P.boundary ℝ ⊆ {x | B x = 0} := by
    intro x hx
    change A x - c = 0
    exact sub_eq_zero.mpr (hsection.subset hx).2
  let Q := P.affineImage r.toAffineMap
  have hQ : Function.Injective Q ∧ Q.HasSimplicialEdges ∧
      a '' Q.boundary ℝ = P.boundary ℝ :=
    P.affineImage_of_leftInvOn hP hPinj r.toAffineMap a.toAffineMap
      (fun x hx => hright (hboundaryplane hx))
  let d : Set E := a '' closure Q.inside
  have hdP : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ) := by
    have h := (Q.isFinitePLBallPair_closed_inside hQ.2.1 hQ.1).affine_image
      a hleft.injective.injOn
    rwa [hQ.2.2] at h
  have hdplaneB : d ⊆ {x | B x = 0} := by
    rintro _ ⟨y, _, rfl⟩
    exact ha y
  have hdplane : d ⊆ {x | A x = c} := by
    intro x hx
    have h := hdplaneB hx
    change A x - c = 0 at h
    exact sub_eq_zero.mp h
  have hd : IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = c}) := by
    rwa [hsection] at hdP
  refine ⟨d, hd, hdplane, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      exact ⟨hx.2, hdplane hx.1⟩
    · intro x hx
      exact ⟨hd.1 hx, hx.1⟩
  · intro C hC hSC
    exact hdP.subset_convex_of_planar_polygon_boundary P hP hPinj B hB hdim
      hdplaneB hC (by
        rintro _ ⟨i, rfl⟩
        exact hSC (hsection.subset (P.vertex_mem_boundary i)).1)






theorem exists_planar_disk_family_of_whole_level_polygons
    (hdim : Module.finrank ℝ E = 3) (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    {S : Set E} {m M : ℝ}
    (hpolygons : ∀ c ∈ Ioo m M, ∃ (n : ℕ) (P : Polygon E (n + 3)),
      P.HasSimplicialEdges ∧ Function.Injective P ∧
        P.boundary ℝ = S ∩ {x | A x = c}) :
    ∃ disks : ℝ → Set E, ∀ c ∈ Ioo m M,
      IsFinitePLBallPair (ℝ × ℝ) (disks c) (S ∩ {x | A x = c}) ∧
      disks c ⊆ {x | A x = c} ∧ disks c ∩ S = S ∩ {x | A x = c} ∧
      ∀ C : Set E, Convex ℝ C → S ⊆ C → disks c ⊆ C := by
  classical
  have hlevel (c : Ioo m M) : ∃ d : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = (c : ℝ)}) ∧
      d ⊆ {x | A x = (c : ℝ)} ∧ d ∩ S = S ∩ {x | A x = (c : ℝ)} ∧
      ∀ C : Set E, Convex ℝ C → S ⊆ C → d ⊆ C := by
    obtain ⟨n, P, hP, hPinj, hsection⟩ := hpolygons c c.property
    exact exists_planar_disk_of_whole_level_polygon hdim A hA P hP hPinj hsection
  choose d hd using hlevel
  let disks : ℝ → Set E := fun c => if hc : c ∈ Ioo m M then d ⟨c, hc⟩ else ∅
  refine ⟨disks, ?_⟩
  intro c hc
  dsimp only [disks]
  rw [dif_pos hc]
  exact hd ⟨c, hc⟩

end PoincareConjecture.M76.ZeroChargeJoint
