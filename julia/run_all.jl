# Runs every check:   julia run_all.jl
# Ends with "N checks passed, 0 failed" and the total runtime.
const T0 = time()
include(joinpath(@__DIR__, "common.jl"))
for f in ("check_network.jl", "check_size.jl", "check_ilp.jl", "check_valuation.jl",
          "check_cauchy.jl", "check_hermite.jl", "check_packing.jl", "check_constants.jl", "check_tree.jl")
    include(joinpath(@__DIR__, f))
end
part_A(); part_B(); part_C(); part_D(); part_E(); part_F(); part_G(); part_H(); part_I()
summary_line()
println("total runtime: ", round(time() - T0, digits=1), " s")
exit(COUNTS[:fail] == 0 ? 0 : 1)
