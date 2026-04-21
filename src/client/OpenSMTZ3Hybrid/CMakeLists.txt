find_package(Z3 CONFIG REQUIRED)

add_executable(solver_opensmt_z3 ../main.cpp SolverProcess.cpp)

target_link_libraries(solver_opensmt_z3 client ${GMP_LIBRARY} ${GMPXX_LIBRARY})

add_executable(z3_smts_proxy Z3SMTSProxy.cpp)
target_include_directories(z3_smts_proxy PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(z3_smts_proxy ${Z3_LIBRARIES})

if (VERBOSE_THREAD)
    target_compile_definitions(solver_opensmt_z3 PUBLIC -DVERBOSE_THREAD)
endif()
