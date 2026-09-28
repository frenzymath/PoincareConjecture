import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.Extensions











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Homothety

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M] {g : RiemannianMetric n M}


noncomputable def curvatureDirectionsBilin (D : LeviCivitaData g) (x : M)
    (w : TangentSpace (𝓡 n) x) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x := by
  have hDZ : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (fun p ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q)
        p (D.connection (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) p)) x := by
    obtain ⟨U, hU, hx, _, _, hw⟩ := exists_open_smooth_extensions x 0 0 w
    exact ((connection_contMDiffOn g D U hU _ hw).contMDiffAt
      (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  exact TensorialAt.mkHom₂ (I := 𝓡 n) (F := EuclideanSpace ℝ (Fin n))
    (F' := EuclideanSpace ℝ (Fin n))
    (fun X Y ↦ D.curvatureOnFields X Y (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) w) x)
    x (fun Y _ ↦ curvatureOnFields_tensorial_first D Y _ x hDZ)
    (fun X _ ↦ curvatureOnFields_tensorial_second D X _ x hDZ)

theorem curvatureDirectionsBilin_apply (D : LeviCivitaData g) (x : M)
    (w u v : TangentSpace (𝓡 n) x) :
    curvatureDirectionsBilin D x w u v = D.curvature x u v w := rfl

theorem curvature_add_first (D : LeviCivitaData g) (x : M)
    (u u' v w : TangentSpace (𝓡 n) x) :
    D.curvature x (u + u') v w = D.curvature x u v w + D.curvature x u' v w := by
  change curvatureDirectionsBilin D x w (u + u') v =
    curvatureDirectionsBilin D x w u v + curvatureDirectionsBilin D x w u' v
  rw [map_add, add_apply]

theorem curvature_smul_first (D : LeviCivitaData g) (x : M)
    (c : ℝ) (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x (c • u) v w = c • D.curvature x u v w := by
  change curvatureDirectionsBilin D x w (c • u) v = c • curvatureDirectionsBilin D x w u v
  rw [map_smul, smul_apply]

theorem curvature_add_second (D : LeviCivitaData g) (x : M)
    (u v v' w : TangentSpace (𝓡 n) x) :
    D.curvature x u (v + v') w = D.curvature x u v w + D.curvature x u v' w := by
  exact (curvatureDirectionsBilin D x w u).map_add v v'

theorem curvature_smul_second (D : LeviCivitaData g) (x : M)
    (c : ℝ) (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u (c • v) w = c • D.curvature x u v w := by
  exact (curvatureDirectionsBilin D x w u).map_smul c v


theorem curvature_bianchi (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w + D.curvature x v w u + D.curvature x w u v = 0 := by
  obtain ⟨U, hU, hx, hu, hv, hw⟩ := exists_open_smooth_extensions x u v w
  exact curvatureOnFields_bianchi D U hU _ _ _ hu hv hw x hx

theorem curvature_eq_neg_cyclic (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w = -(D.curvature x v w u + D.curvature x w u v) := by
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using curvature_bianchi D x u v w)

theorem curvature_add_third (D : LeviCivitaData g) (x : M)
    (u v w w' : TangentSpace (𝓡 n) x) :
    D.curvature x u v (w + w') = D.curvature x u v w + D.curvature x u v w' := by
  rw [curvature_eq_neg_cyclic D x u v (w + w'), curvature_add_second, curvature_add_first,
    curvature_eq_neg_cyclic D x u v w, curvature_eq_neg_cyclic D x u v w']
  abel

theorem curvature_smul_third (D : LeviCivitaData g) (x : M)
    (c : ℝ) (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v (c • w) = c • D.curvature x u v w := by
  rw [curvature_eq_neg_cyclic D x u v (c • w), curvature_smul_second, curvature_smul_first,
    curvature_eq_neg_cyclic D x u v w, smul_neg, smul_add]


noncomputable def curvatureTensorLinear (D : LeviCivitaData g) (x : M) :
    TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ]
      TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v ↦
        { toFun := fun w ↦
            { toFun := fun z ↦ D.curvatureTensor x u v w z
              map_add' := fun z z' ↦ by
                simp only [LeviCivitaData.curvatureTensor, curvature_add_third, map_add,
                  add_apply]
              map_smul' := fun c z ↦ by
                simp only [LeviCivitaData.curvatureTensor, curvature_smul_third, map_smul,
                  smul_apply, smul_eq_mul, RingHom.id_apply] }
          map_add' := fun w w' ↦ by
            ext z
            exact (g.inner x (D.curvature x u v z)).map_add w w'
          map_smul' := fun c w ↦ by
            ext z
            exact (g.inner x (D.curvature x u v z)).map_smul c w }
      map_add' := fun v v' ↦ by
        ext w z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
          LeviCivitaData.curvatureTensor, curvature_add_second, map_add,
          add_apply]
      map_smul' := fun c v ↦ by
        ext w z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
          LeviCivitaData.curvatureTensor, curvature_smul_second, map_smul,
          smul_apply, smul_eq_mul, RingHom.id_apply] }
  map_add' u u' := by
    ext v w z
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      LeviCivitaData.curvatureTensor, curvature_add_first, map_add,
      add_apply]
  map_smul' c u := by
    ext v w z
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      LeviCivitaData.curvatureTensor, curvature_smul_first, map_smul,
      smul_apply, smul_eq_mul, RingHom.id_apply]

theorem curvatureTensorLinear_apply (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    curvatureTensorLinear D x u v w z = D.curvatureTensor x u v w z := rfl

end PoincareConjecture.Homothety
