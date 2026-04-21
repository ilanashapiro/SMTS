add_executable(solver_opensmt_z3 ../main.cpp SolverProcess.cpp)

target_link_libraries(solver_opensmt_z3 client ${GMP_LIBRARY} ${GMPXX_LIBRARY})

if (VERBOSE_THREAD)
    target_compile_definitions(solver_opensmt_z3 PUBLIC -DVERBOSE_THREAD)
endif()
