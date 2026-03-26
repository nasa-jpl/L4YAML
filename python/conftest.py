"""Pytest configuration for lean4yaml tests.

Blocks ROS 2 launch_testing plugins that conflict with standalone pytest.
"""
# Unregister problematic plugins that register unknown hooks
def pytest_configure(config):
    pm = config.pluginmanager
    for name in ("launch_testing_ros_pytest_entrypoint", "launch_testing"):
        if pm.has_plugin(name):
            pm.unregister(name=name)
        plugin = pm.get_plugin(name)
        if plugin is not None:
            pm.unregister(plugin=plugin, name=name)
