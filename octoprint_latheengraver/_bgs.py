#!/usr/bin/python
# -*- coding: utf-8 -*-
#
# Written by:  Shell M. Shrader (https://github.com/synman/Octoprint-Bettergrblsupport)
# Copyright [2021] [Shell M. Shrader]
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# References
#
# https://web.archive.org/web/20211123161339/https://wiki.shapeoko.com/index.php/G-Code
# https://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=B69BCE8C0F7F5071B56B464AB4CA8C56?doi=10.1.1.15.7813&rep=rep1&type=pdf
# https://github.com/gnea/grbl/blob/master/doc/markdown/commands.md
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Jogging
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Configuration#10---status-report-mask
# https://github.com/gnea/grbl/wiki/Grbl-v1.1-Interface#grbl-push-messages
# https://reprap.org/wiki/G-codeimport os
#
from operator import truediv
import os
import time
import math

import re
import requests
import threading

from timeit import default_timer as timer
from octoprint.events import Events
from octoprint.access.permissions import Permissions


def load_grbl_descriptions(_plugin):
    path = os.path.dirname(os.path.realpath(__file__)) + os.path.sep + "static" + os.path.sep + "txt" + os.path.sep

    f = open(path + "grbl_errors.txt", 'r')

    for line in f:
        match = re.search(r"^(-?[\d\.]+)[\ ]+(-?[\S\ ]*)", line)
        if not match is None:
            _plugin.grblErrors[int(match.groups(1)[0])] = match.groups(1)[1]
            # _plugin._logger.debug("matching error id: [%d] to description: [%s]", int(match.groups(1)[0]), match.groups(1)[1])

    f = open(path + "grbl_alarms.txt", 'r')

    for line in f:
        match = re.search(r"^(-?[\d\.]+)[\ ]+(-?[\S\ ]*)", line)
        if not match is None:
            _plugin.grblAlarms[int(match.groups(1)[0])] = match.groups(1)[1]
            # _plugin._logger.debug("matching alarm id: [%d] to description: [%s]", int(match.groups(1)[0]), match.groups(1)[1])

    f = open(path + "grbl_settings.txt", 'r')

    for line in f:
        match = re.search(r"^(-?[\d\.]+)[\ ]+(-?[\S\ ]*)", line)
        if not match is None:
            _plugin.grblSettingsNames[int(match.groups(1)[0])] = match.groups(1)[1]
            # _plugin._logger.debug("matching setting id: [%d] to description: [%s]", int(match.groups(1)[0]), match.groups(1)[1])


def load_grbl_settings(_plugin):
    _plugin._logger.debug("_bgs: load_grbl_settings")

    _plugin.grblSettingsText = _plugin._settings.get(["grblSettingsText"])

    if not _plugin.grblSettingsText is None:
        for setting in _plugin.grblSettingsText.split("||"):
            if len(setting.strip()) > 0:

                _plugin._logger.debug("load_grbl_settings=[{}]".format(setting))

                set = setting.split("|")
                if not set is None:
                    _plugin.grblSettings.update({int(set[0]): [set[1], _plugin.grblSettingsNames.get(int(set[0]))]})
    return


def save_grbl_settings(_plugin):
    _plugin._logger.debug("_bgs: save_grbl_settings")

    ret = ""
    for id, data in sorted(_plugin.grblSettings.items(), key=lambda x: int(x[0])):
        ret = ret + "{}|{}|{}||".format(id, data[0], data[1])

    _plugin._logger.debug("save_grbl_settings=[{}]".format(ret))

    _plugin.grblSettingsText = ret

    return ret


def cleanup_due_to_uninstall(_plugin, remove_profile=True):
    _plugin._logger.debug("_bgs: cleanup_due_to_uninstall remove_profile=[{}]".format(remove_profile))

    # re-enable model size detection, sd card support
    _plugin._settings.global_set_boolean(["feature", "modelSizeDetection"], True)
    _plugin._settings.global_set_boolean(["feature", "sdSupport"], True)

    # load maps of disabled plugins & tabs
    disabledPlugins = _plugin._settings.global_get(["plugins", "_disabled"])
    disabledTabs = _plugin._settings.global_get(["appearance", "components", "disabled", "tab"])
    orderedTabs = _plugin._settings.global_get(["appearance", "components", "order", "tab"])
    orderedSidebar = _plugin._settings.global_get(["appearance", "components", "order", "sidebar"])

    if disabledPlugins == None:
        disabledPlugins = []

    if disabledTabs == None:
        disabledTabs = []

    if orderedTabs == None:
        orderedTabs = []

    if orderedSidebar == None:
        orderedSidebar = []

    # re-enable the printer safety check plugin
    if "printer_safety_check" in disabledPlugins:
        disabledPlugins.remove("printer_safety_check")

    # re-enable the gcodeviewer plugin
    if "gcodeviewer" in disabledPlugins:
        disabledPlugins.remove("gcodeviewer")
    if "plugin_gcodeviewer" in disabledTabs:
        disabledTabs.remove("plugin_gcodeviewer")

    # re-enable the built-in temp tab if it was hidden
    if "temperature" in disabledTabs:
        disabledTabs.remove("temperature")

    # re-enable the built-in control tab if it was hidden
    if "control" in disabledTabs:
        disabledTabs.remove("control")

    # remove me from ordered tabs if i'm in there
    if "plugin_bettergrblsupport" in orderedTabs:
        orderedTabs.remove("plugin_bettergrblsupport")

    # remove me from ordered sidebar if i'm in there
    if "plugin_bettergrblsupport" in orderedSidebar:
        orderedSidebar.remove("plugin_bettergrblsupport")

    if remove_profile:
        # restore the original printer profile (if it exists) and delete mine
        old_profile = _plugin._settings.get(["old_profile"])

        if not old_profile or not _plugin._printer_profile_manager.exists(old_profile):
            old_profile = "_default"

        _plugin._printer_profile_manager.select(old_profile)
        _plugin._printer_profile_manager.set_default(old_profile)

        if _plugin._printer_profile_manager.exists("_bgs"):
            _plugin._printer_profile_manager.remove("_bgs")
            _plugin._logger.debug("bgs profile has been deleted")

    _plugin._settings.global_set(["plugins", "_disabled"], disabledPlugins)
    _plugin._settings.global_set(["appearance", "components", "disabled", "tab"], disabledTabs)
    _plugin._settings.global_set(["appearance", "components", "order", "tab"], orderedTabs)
    _plugin._settings.global_set(["appearance", "components", "order", "sidebar"], orderedSidebar)

    # add pretty much all of grbl to long running commands list
    longCmds = _plugin._settings.global_get(["serial", "longRunningCommands"])
    if longCmds == None: longCmds = []

    if "$H" in longCmds: longCmds.remove("$H")
    if "G92" in longCmds: longCmds.remove("G92")
    if "G30" in longCmds: longCmds.remove("G30")
    if "G53" in longCmds: longCmds.append("G53")
    if "G54" in longCmds: longCmds.remove("G54")

    if "G20" in longCmds: longCmds.remove("G20")
    if "G21" in longCmds: longCmds.remove("G21")

    if "G90" in longCmds: longCmds.remove("G90")
    if "G91" in longCmds: longCmds.remove("G91")

    if "G38.1" in longCmds: longCmds.remove("G38.1")
    if "G38.2" in longCmds: longCmds.remove("G38.2")
    if "G38.3" in longCmds: longCmds.remove("G38.3")
    if "G38.4" in longCmds: longCmds.remove("G38.4")
    if "G38.5" in longCmds: longCmds.remove("G38.5")

    if "G0" in longCmds: longCmds.remove("G0")
    if "G1" in longCmds: longCmds.remove("G1")
    if "G2" in longCmds: longCmds.remove("G2")
    if "G3" in longCmds: longCmds.remove("G3")
    if "G4" in longCmds: longCmds.remove("G4")

    if "M3" in longCmds: longCmds.remove("M3")
    if "M4" in longCmds: longCmds.remove("M4")
    if "M5" in longCmds: longCmds.remove("M5")
    if "M7" in longCmds: longCmds.remove("M7")
    if "M8" in longCmds: longCmds.remove("M8")
    if "M9" in longCmds: longCmds.remove("M9")
    if "M30" in longCmds: longCmds.remove("M30")

    _plugin._settings.global_set(["serial", "longRunningCommands"], longCmds)
    _plugin._settings.global_set(["serial", "maxCommunicationTimeouts", "long"], 5)
    _plugin._settings.global_set_boolean(["serial", "neverSendChecksum"], False)
    _plugin._settings.global_set(["serial", "encoding"], "ascii")
    _plugin._settings.global_set_boolean(["serial", "sanityCheckTools"], True)

    _plugin._settings.global_set(["terminalFilters"], _plugin.octo_filters)
    
    _plugin._settings.save()

    # remove scripts/gcode/afterPrintCancelled because it does stupid stuff with tools
    oldCancelScript = os.path.realpath(os.path.join(_plugin._settings.global_get_basefolder("scripts"), "gcode", "oldAfterPrintCancelled"))
    currentCancelScript = os.path.realpath(os.path.join(_plugin._settings.global_get_basefolder("scripts"), "gcode", "afterPrintCancelled"))

    if os.path.exists(oldCancelScript) and not os.path.exists(currentCancelScript):
        os.rename(oldCancelScript, currentCancelScript)


# #-- EventHandlerPlugin mix-in
def on_event(_plugin, event, payload):
    subscribed_events = (Events.FILE_SELECTED, Events.FILE_ADDED, Events.PRINT_STARTED, Events.PRINT_CANCELLED, Events.PRINT_CANCELLING,
                        Events.PRINT_PAUSED, Events.PRINT_RESUMED, Events.PRINT_DONE, Events.PRINT_FAILED,
                        Events.PLUGIN_PLUGINMANAGER_UNINSTALL_PLUGIN, Events.PLUGIN_PLUGINMANAGER_DISABLE_PLUGIN, Events.UPLOAD,
                        Events.CONNECTING, Events.CONNECTED, Events.DISCONNECTING, Events.DISCONNECTED, Events.STARTUP, Events.SHUTDOWN)

    if event not in subscribed_events and payload is not None and payload.get("state_id") not in ("PAUSING", "STARTING"):
        #_plugin._logger.debug('event [{}] received but not subscribed - discarding'.format(event))
        return

    _plugin._logger.debug("_bgs: on_event event=[{}] payload=[{}]".format(event, payload))

    # our plugin is being uninstalled
    if event in (Events.PLUGIN_PLUGINMANAGER_UNINSTALL_PLUGIN, Events.PLUGIN_PLUGINMANAGER_DISABLE_PLUGIN) and payload["id"] == _plugin._identifier:
        _plugin._logger.debug('we are being uninstalled/disabled :(')
        cleanup_due_to_uninstall(_plugin)
        _plugin._logger.debug('plugin cleanup completed (this house is clean)')
        return

    if _plugin._printer_profile_manager.get_current_or_default()["id"] != "_bgs":
        return

    # - CONNECTING
    if event == Events.CONNECTING:
        _plugin.connectionState = event
        # let's make sure we don't have any commands queued up
        _plugin.grblCmdQueue.clear()

    # - CONNECTED
    if event == Events.CONNECTED:
        _plugin._logger.debug('machine connected')

        _plugin.connectionState = event
        _plugin.whenConnected = time.time()
        _plugin.autoSleepTimer = time.time()

        _plugin.is_operational = True
        _plugin._settings.set_boolean(["is_operational"], _plugin.is_operational)

        _plugin.fluidConfig = None
        _plugin._printer.commands(["$I", "$G"])
        _plugin.RTCM = False
        # _plugin._printer.fake_ack()

    # Disconnecting & Disconnected
    if event in (Events.DISCONNECTING, Events.DISCONNECTED):
        _plugin.connectionState = event
        _plugin.handshakeSent = False
        _plugin.grblState = "N/A"
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="N/A"))

        _plugin.is_operational = False
        _plugin._settings.set_boolean(["is_operational"], _plugin.is_operational)

    # Print Starting
    if payload is not None and payload.get("state_id") == "STARTING":
        add_notifications(_plugin, ["Pgm Begin"])
        # threading.Thread(target=send_command_now, args=(_plugin._printer, _plugin._logger, "?")).start()
        _plugin._printer.commands("?", force=True)
        # reset our rate/position overrides
        # DO NOT INCLUDE CRITICAL THINGS HERE.THIS EVENT WILL OCCUR AFTER COMMANDS ARE ALREADY SENT
        return

    # 'PrintStarted'
    if event == Events.PRINT_STARTED:
        if "HOLD" in _plugin.grblState.upper():
            _plugin._printer.commands(["~"], force=True)
        elif not _plugin.grblState.upper() in ("IDLE", "CHECK"):
            # we have to stop This
            _plugin._logger.debug("cancelling job,state is: {0}".format(_plugin.grblState))
            _plugin._printer.cancel_print()
            return



        _plugin.grblState = "Run"
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="Run"))

        _plugin.is_printing = True
        _plugin._settings.set_boolean(["is_printing"], _plugin.is_printing)

        #these should never be on in lasermode
        #if is_laser_mode(_plugin):
        #    _plugin.template = False
        #    _plugin.track_plunge =False
        
        if _plugin.autoCooldown:
            activate_auto_cooldown(_plugin)
        #Get Machine positions to log starting positions
        #_plugin._printer.commands(["$10=156","?"],force=True)
        return

    # Print ended (finished / failed / cancelled)
    if event in (Events.PRINT_CANCELLED, Events.PRINT_DONE, Events.PRINT_FAILED):
        # DO NOT INCLUDE CRITICAL THINGS HERE.THIS EVENT WILL OCCUR AFTER COMMANDS ARE ALREADY SENT
        _plugin.grblState = "Idle"
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="Idle"))
        _plugin.feedRate = 0.0
        _plugin.is_printing = False
        _plugin._settings.set_boolean(["is_printing"], _plugin.is_printing)
        _plugin.TERMINATE = False
        _plugin._printer.fake_ack()
        _plugin._logger.debug('Made it through cancel, done failed')
        return

    # Print Cancelling
    if event == Events.PRINT_CANCELLING:
        _plugin._logger.debug("cancelling job")

        if "HOLD" in _plugin.grblState.upper():
            _plugin._printer.commands(["M999","M5"], force=True)
        else:
            _plugin._printer.commands(["~","M5"], force=True)

    # Print Pausing
    if payload is not None and payload.get("state_id") == "PAUSING":
        _plugin._logger.debug("pausing job")
        _plugin.pausedPower = _plugin.grblPowerLevel
        _plugin.pausedPositioning = _plugin.positioning


    # Print Paused
    if event == Events.PRINT_PAUSED:
        _plugin._printer.set_job_on_hold(False)
        _plugin._logger.debug("paused job")
        #_plugin._printer.commands(["M5", "?", "!", "?"], force=True)

    # Print Resumed
    if event == Events.PRINT_RESUMED:
        _plugin._logger.debug("resuming job")

        """
        _plugin._printer.commands(["~","M3","G4 P5"], tags={"script:beforePrintResumed"}, force=True)

        _plugin._printer.commands(["~", "M3", "G4 P5"], force=True)

        # move our spindle back down 5
        #if not is_laser_mode(_plugin):
        #    _plugin._printer.commands(["G4 P10", "G91 G0 Z-5"], force=True)


        # make sure we are using whatever positioning mode was active before we paused
        _plugin._printer.commands(["G91" if _plugin.pausedPositioning == 1 else "G90"], tags={"script:beforePrintResumed"},force=True)
        
        #only send if there is a queued command
        if _plugin.queued_command:
            _plugin._printer.commands(["{0}".format(_plugin.queued_command)], tags={"script:beforePrintResumed"}, force=True)
            _plugin.queued_command = ""

        """
        _plugin.grblState = "Run"
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state", state="Run"))

    # starting up
    if event == Events.STARTUP:
        _plugin._logger.info("starting up")

    # shutting down
    if event == Events.SHUTDOWN:
        _plugin._logger.info("shutting down")
        _plugin._settings.save()

    # File uploaded
    if event == Events.UPLOAD:
        if payload["path"].endswith(".gc") or payload["path"].endswith(".nc"):
            renamed_file = payload["path"][:len(payload["path"]) - 2] + "gcode"

            _plugin._logger.debug("renaming [%s] to [%s]", payload["path"], renamed_file)

            _plugin._file_manager.remove_file(payload["target"], renamed_file)
            _plugin._file_manager.move_file(payload["target"], payload["path"], renamed_file)

            generate_metadata_for_file(_plugin, renamed_file, notify=False, force=True)

    # 'FileAdded'
    if event == Events.FILE_ADDED:
        generate_metadata_for_file(_plugin, payload["path"], notify=False, force=True)

    # 'FileSelected'
    if event == Events.FILE_SELECTED:
        generate_metadata_for_file(_plugin, payload["path"], notify=True)
        return

    if event == Events.FILE_DESELECTED:
        return

    return

def toggle_weak(_plugin):
    _plugin._logger.debug("_bgs: toggle_weak")

    f = max(get_axes_max_rates(_plugin))

    if _plugin.grblPowerLevel == 0:
        # turn on laser in weak mode
        _plugin._printer.commands("G1 F{} M3 S{:.2f}".format(f, _plugin.weakLaserValue))
        add_notifications(_plugin, ["Weak laser enabled"])
        res = "Laser Off"
    else:
        _plugin._printer.commands(["M3 S0", "M5", "G0"])
        add_notifications(_plugin, ["Weak laser disabled"])
        res = "Weak Laser"

    return res


def process_grbl_status_msg(_plugin, msg):
    #need to redefine much of this if we have more axes
    hasA = _plugin._settings.get(["hasA"])
    hasB = _plugin._settings.get(["hasB"])
    match = re.search(r'<(-?[^,]+)[,|][WM]Pos:(-?[\d\.]+),(-?[\d\.]+),(-?[\d\.]+),?(-?[\d\.]+)?,?(-?[\d\.]+)?', msg)
    #response = 'X:{1} Y:{2} Z:{3} E:0 {original}'.format(*match.groups(), original=msg)
    response = 'X:{1} Y:{2} Z:{3} E:0 '.format(*match.groups())
    _plugin.grblMode = "MPos" if "MPos" in msg else "WPos" if "WPos" in msg else "N/A"
    _plugin.grblState = str(match.groups(1)[0])
    _plugin.grblX = float(match.groups(1)[1])
    _plugin.grblY = float(match.groups(1)[2])
    _plugin.grblZ = float(match.groups(1)[3])

    if match.groups(1)[5]:
        _plugin.grblA = float(match.groups(1)[4])
        _plugin.grblB = float(match.groups(1)[5])
        response = response+'A:{0} B:{1} '.format(_plugin.grblA, _plugin.grblB)
    if match.groups(1)[4] and not match.groups(1)[5] and hasB:
        _plugin.grblB = float(match.groups(1)[4])
        reponse = response+'B:{0}'.format(_plugin.grblB)
    else:
        _plugin.grblA = float(match.groups(1)[4])
        response = response+'A:{0} '.format(_plugin.grblA)
    response = response+msg

    match = re.search(r'.*\|Pn:([XYZABPDHRS]+)', msg)
    if not match is None:
        _plugin.grblActivePins = match.groups(1)[0]
    else:
        _plugin.grblActivePins = "None"

    match = re.search(r'.*\|FS:(-?[\d\.]+),(-?[\d\.]+)', msg)
    if not match is None:
        _plugin.grblSpeed = round(float(match.groups(1)[0]))
        _plugin.grblPowerLevel = float(match.groups(1)[1])

    _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state",
                                                                    mode=_plugin.grblMode,
                                                                    state=_plugin.grblState,
                                                                    x=_plugin.grblX,
                                                                    y=_plugin.grblY,
                                                                    z=_plugin.grblZ,
                                                                    a=_plugin.grblA,
                                                                    b=_plugin.grblB,
                                                                    pins=_plugin.grblActivePins,
                                                                    speed=_plugin.grblSpeed,
                                                                    power=_plugin.grblPowerLevel,
                                                                    coord=_plugin.grblCoordinateSystem,
                                                                    coolant=_plugin.coolant,
                                                                    positioning=_plugin.positioning))

    # odd edge case where a machine could be asleep or holding while connecting
    # TODO: this may no longer be valid given refactoring
    if not _plugin._printer.is_operational() and _plugin.grblState.upper() in ("SLEEP", "HOLD:0", "HOLD:1", "DOOR:0", "DOOR:1"):
        _plugin._printer.commands("M999", force=True)

    # pop any queued commands if state is IDLE or HOLD:0, DOOR:0, CHECK, or ALARM
    if len(_plugin.grblCmdQueue) > 0 and _plugin.grblState.upper() in ("IDLE", "HOLD:0", "DOOR:0", "CHECK", "ALARM"):
        _plugin._logger.debug('sending queued command [%s] - depth [%d]', _plugin.grblCmdQueue[0], len(_plugin.grblCmdQueue))
        _plugin._printer.commands(_plugin.grblCmdQueue[0])
        _plugin.grblCmdQueue.pop(0)

    # add a notification if we just homed
    if _plugin.grblState.upper() == "HOME":
        add_notifications(_plugin, ["Machine has been homed"])

    # the only thing useful remaining is buffer stats
    # and we currently don't do anything with it
    # for stat in msg.replace("<", "").replace(">", "").split("|"):
    #     # buffer stats and Pin stats
    #     if stat.startswith("Bf:") or stat.startswith("Pn:"):
    #         _plugin.add_to_notify_queue(stat)

    return response


def process_grbl_alarm(_plugin, msg):
    error = int(0)
    desc = msg

    match = re.search(r'alarm:\ *(-?[\d.]+)', msg.lower())
    if not match is None:
        error = int(match.groups(1)[0])
        desc = _plugin.grblAlarms.get(error)

    _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="simple_notify",
                                                                    title="Grbl Alarm #{} Received".format(error),
                                                                    text=desc,
                                                                    hide=True,
                                                                    delay=10000,
                                                                    notify_type="notice"))

    _plugin._logger.warning("alarm received: %d: %s", error, _plugin.grblAlarms.get(error))

    # inform _bgs in case it has something going on (probing)
    grbl_alarm_or_error_occurred(_plugin)

    # clear out any pending queued Commands
    if len(_plugin.grblCmdQueue) > 0:
        _plugin._logger.debug("clearing %d commands from the command queue", len(_plugin.grblCmdQueue))
        _plugin.grblCmdQueue.clear()

    # put a message on our notification queue and force an inquiry
    add_notifications(_plugin, [desc])
    _plugin._printer.commands("?")

    # we need to pause if we are printing
    if _plugin._printer.is_printing():
        _plugin._printer.pause_print()

    # our sync buffers are no longer reliable
    _plugin.lastRequest = []
    _plugin.lastResponse = ""

    # return 'Error: ' + desc
    return "ok " + desc


def process_grbl_error(_plugin, msg):
    error = int(0)
    desc = msg

    match = re.search(r'error:\ *(-?[\d.]+)', msg.lower())
    if not match is None:
        error = int(match.groups(1)[0])

        desc = _plugin.grblErrors.get(error)
        if desc is None: desc = "Grbl Error #{} - Error description not available".format(error)

    # hack to suppress errors on connect
    if time.time() - _plugin.whenConnected < 20: return "ok "

    # lets not deal with file not found
    if error == 65: return "ok "

    _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="simple_notify",
                                                                    title="Grbl Error #{} Received".format(error),
                                                                    text=desc,
                                                                    hide=True,
                                                                    delay=10000,
                                                                    notify_type="error"))
    _plugin._logger.warning("error received: %d: %s", error, desc)

    # inform _bgs in case it has something going on (probing)
    grbl_alarm_or_error_occurred(_plugin)

    # # clear out any pending queued Commands
    # if len(_plugin.grblCmdQueue) > 0:
    #     _plugin._logger.debug("clearing %d commands from the command queue", len(_plugin.grblCmdQueue))
    #     _plugin.grblCmdQueue.clear()

    # our sync buffers are no longer reliable
    _plugin.lastRequest = []
    _plugin.lastResponse = ""

    # put a message on our notification queue and force an inquiry
    add_notifications(_plugin, [desc])
    # _plugin._printer.commands("?")

    # we need to pause if we are printing
    if _plugin._printer.is_printing():
        _plugin._printer.pause_print()

    # don't tell octoprint because it will freak out
    return "ok "


def process_parser_status_msg(_plugin, msg):
    parserState = msg.replace("[", "").replace("]", "").replace("GC:", "")

    for state in parserState.split(" "):
        if state in ("G90", "G91"):
            _plugin.positioning = int(state[2:3])
            _plugin._logger.debug("parser state indicates [%s] distance mode", "absolute" if _plugin.positioning == 0 else "relative")

        elif state in ("G0", "G1", "G2", "G3", "G38.2", "G38.3", "G38.4", "G38.5", "G80"):
            _plugin._logger.debug("parser state indicates [%s] motion mode", state)
        elif state in ("G54", "G55", "G56", "G57", "G58", "G59"):
            _plugin.grblCoordinateSystem = state
            _plugin._logger.debug("parser state indicates [%s] coordinate system active", _plugin.grblCoordinateSystem)
        elif state in ("G17", "G18", "G19"):
            _plugin._logger.debug("parser state indicates [%s] plane selected", state)
        elif state in ("G20", "G21"):
            _plugin._logger.debug("parser state indicates [%s] uom active", "metric" if state == "G21" else "imperial")
        elif state in ("G93", "G94"):
            _plugin._logger.debug("parser state indicates [%s] feed rate mode", state)
        elif state in ("M3", "M4", "M5"):
            _plugin._logger.debug("parser state indicates [%s] spindle state", state)
        elif state in ("M7", "M8", "M9"):
            _plugin.coolant = state
            _plugin._logger.debug("parser state indicates [%s] coolant state", state)
        elif state.startswith("F"):
            _plugin.grblSpeed = round(float(state.replace("F", "")))
            _plugin._logger.debug("parser state indicates feed rate of [%d]", _plugin.grblSpeed)
        elif state.startswith("S"):
            _plugin.grblPowerLevel = float(state.replace("S", ""))
            _plugin._logger.debug("parser state indicates spindle speed of [%f]", _plugin.grblPowerLevel)
        elif state.startswith("T"):
            _plugin._logger.debug("parser state indicates tool #[%s] active", state.replace("T", ""))

    _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_state",
                                                                        speed=_plugin.grblSpeed,
                                                                        power=_plugin.grblPowerLevel,
                                                                        coord=_plugin.grblCoordinateSystem,
                                                                        coolant=_plugin.coolant,
                                                                        positioning=_plugin.positioning))

def grbl_alarm_or_error_occurred(_plugin):


    _plugin._logger.debug("_bgs: grbl_alarm_or_error_occurred")



def activate_auto_cooldown(_plugin):
    _plugin._logger.debug("_bgs: activate_auto_cooldown")
    threading.Thread(target=auto_cooldown_monitor, args=(_plugin,)).start()


def auto_cooldown_monitor(_plugin):
    _plugin._logger.debug("_bgs: auto_cooldown_monitor")

    frequency = _plugin.autoCooldownFrequency * 60
    duration = _plugin.autoCooldownDuration * 60

    while _plugin._printer.is_printing():
        _plugin._logger.debug("auto cooldown loop started")

        startTime = time.time()

        while _plugin._printer.is_printing() and time.time() < startTime + frequency:
            time.sleep(1)

        if _plugin._printer.is_printing():
            _plugin._logger.debug("auto cooldown pausing job")
            _plugin._printer.pause_print()
        else:
            _plugin._logger.debug("job appears to have unexpectedly ended while waiting for cooldown frequency")
            break

        startTime = time.time()

        while (_plugin._printer.is_pausing() or _plugin._printer.is_paused()) and time.time() < startTime + duration:
            time.sleep(1)

        if _plugin._printer.is_paused():
            _plugin._logger.debug("auto cooldown resuming job")
            _plugin._printer.resume_print()
        else:
            _plugin._logger.debug("job appears to have unexpectedly ended while waiting for cooldown duration")
            continue

        _plugin._logger.debug("auto cooldown loop complete")
    _plugin._logger.debug("auto cooldown monitor shutting down")


def queue_cmds_and_send(_plugin, cmds, wait=False):
    _plugin._logger.debug("_bgs: queue_cmds_and_send cmds=[{}] wait=[{}]".format(cmds, wait))

    for cmd in cmds:
        _plugin._logger.debug("queuing command [%s] wait=%r", cmd, wait)
        _plugin.grblCmdQueue.append(cmd)

    if wait:
        wait_for_empty_cmd_queue(_plugin)


def wait_for_empty_cmd_queue(_plugin):
    _plugin._logger.debug("_bgs: wait_for_empty_cmd_queue")

    while len(_plugin.grblCmdQueue) > 0:
        time.sleep(.001)

    _plugin._logger.debug("done waiting for command queue to drain")


def add_notifications(_plugin, notifications):
    _plugin._logger.debug("_bgs: add_notifications notifications=[{}]".format(notifications))


    for notification in notifications:
        _plugin.notifications.append((time.time(), notification))
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="notification", message=notification))


def generate_metadata_for_file(_plugin, filename, notify=False, force=False):
    metadata = _plugin._file_manager.get_metadata("local", filename)
    created = os.path.getctime(_plugin._file_manager.path_on_disk("local", filename))

    processing = True if metadata.get("bgs_processing") == "true" else False
    length = metadata.get("bgs_length")
    width = metadata.get("bgs_width")
    origin = metadata.get("bgs_origin")
    timestamp = metadata.get("bgs_timestamp")

    if timestamp is None or created > timestamp:
        force = True

    _plugin._logger.debug("_bgs: generate_metadata_for_file filename=[{}] notify=[{}] force=[{}] processing=[{}] length=[{}] width=[{}] origin=[{}]".format(filename, notify, force, processing, length, width, origin))

    if length is None or width is None or origin is None or force:
        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_width")
        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_length")
        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_origin")

        if processing and notify:
            threading.Thread(target=wait_for_metadata_processing, args=(_plugin, filename, notify)).start()
        else:
            _plugin._file_manager.set_additional_metadata("local", filename, "bgs_processing", "true", overwrite=True)
            threading.Thread(target=defer_generate_metadata_for_file, args=(_plugin, filename, notify)).start()
    else:
        if notify:
            _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_frame_size",
                                                                                 length=length,
                                                                                  width=width,
                                                                                  origin=origin))

def defer_generate_metadata_for_file(_plugin, filename, notify):
    _plugin._logger.debug("_bgs: defer_generate_metadata_for_file filename=[{}] notify=[{}]".format(filename, notify))

    try:
        file = _plugin._file_manager.path_on_disk("local", filename)
        created = os.path.getctime(file)

        f = open(file, 'r')

        minX = float("inf")
        minY = float("inf")
        maxX = float("-inf")
        maxY = float("-inf")

        x = float(0)
        y = float(0)

        overX = False
        overY = False
        underX = False
        underY = False

        lastGCommand = ""
        positioning = _plugin.positioning
        origin = ""

        start = timer()

        for line in f:
            # skip comments / etc
            if line.upper().lstrip().startswith((";", "(", "%")): continue

            # save our G command for shorthand post processors
            if line.upper().lstrip().startswith("G"):
                lastGCommand = line.lstrip()[:3] if line.lstrip()[2:3].isnumeric() else line.lstrip()[:2]

            # use our saved G command if our line starts with a coordinate
            if line.upper().lstrip().startswith(("X", "Y", "Z")):
                command = lastGCommand.upper() + " " + line.upper().strip()
            else:
                command = line.upper().strip()

            # only G commands matter (except G53)
            if not command.upper().lstrip().startswith("G") or "G53" in command.upper():
                continue

            if "G90" in command.upper():
                # absolute positioning
                positioning = 0

            if "G91" in command.upper():
                # relative positioning
                positioning = 1

            # match = re.search(r"^G([0][0123]|[0123])(\D.*[Xx]|[Xx])\ *(-?[\d.]+).*", command)
            match = re.search(r".*[X]\ *(-?[\d.]+).*", command)
            # _plugin._logger.debug("command=[{}]".format(command))
            if not match is None:
                x = float(match.groups(1)[0]) if positioning == 0 else x + float(match.groups(1)[0])
                if x < minX:
                    if not underX and x < -1:
                        _plugin._logger.debug("underX x=[{}]".format(x))
                        underX = True
                    minX = x
                if x > maxX:
                    if not overX and x > 1:
                        _plugin._logger.debug("overX x=[{}]".format(x))
                        overX = True
                    maxX = x

            # match = re.search(r"^G([0][0123]|[0123])(\D.*[Yy]|[Yy])\ *(-?[\d.]+).*", command)
            match = re.search(r".*[Y]\ *(-?[\d.]+).*", command)
            if not match is None:
                y = float(match.groups(1)[0]) if positioning == 0 else y + float(match.groups(1)[0])
                if y < minY:
                    if not underY and y <= -1:
                        _plugin._logger.debug("underY y=[{}]".format(y))
                        underY = True
                    minY = y
                if y > maxY:
                    if not overY and y > 1:
                        _plugin._logger.debug("overY y=[{}]".format(y))
                        overY = True
                    maxY = y

        length = math.ceil(maxY - minY)
        width = math.ceil(maxX - minX)

        # bottom
        if overY and not underY and overX and not underX: origin = "grblBottomLeft"
        if overY and not underY and overX and underX: origin = "grblBottomCenter"
        if overY and not underY and not overX and underX: origin = "grblBottomRight"

        # center
        if overY and underY and overX and not underX: origin = "grblCenterLeft"
        if overY and underY and overX and underX: origin = "grblCenter"
        if overY and underY and not overX and underX: origin = "grblCenterRight"

        # top
        if not overY and underY and overX and not underX: origin = "grblTopLeft"
        if not overY and underY and overX and underX: origin = "grblTopCenter"
        if not overY and underY and not overX and underX: origin = "grblTopRight"

        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_length", length, overwrite=True)
        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_width", width, overwrite=True)
        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_origin", origin, overwrite=True)
        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_timestamp", created, overwrite=True)
        _plugin._file_manager.set_additional_metadata("local", filename, "bgs_imgurl", "small.png", overwrite=True)

        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_processing")

        _plugin._logger.debug('finished reading file=[{}] length=[{}] width=[{}] origin=[{}] positioning=[{}] time=[{}]'.format(filename, length, width, origin, positioning, timer() - start))

        if notify:
            _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_frame_size",
                                                                             length=length,
                                                                             width=width,
                                                                             origin=origin))
    except BaseException as e:
        _plugin._logger.error("defer_generate_metadata_for_file: [{}]".format(str(e)))

def wait_for_metadata_processing(_plugin, filename, notify):
    _plugin._logger.debug("_bgs: wait_for_metadata_processing filename=[{}] notify=[{}]".format(filename, notify))

    metadata = _plugin._file_manager.get_metadata("local", filename)
    processing = True if metadata.get("bgs_processing") == "true" else False
    seconds = 0

    while seconds < 300 and processing:
        time.sleep(1)
        metadata = _plugin._file_manager.get_metadata("local", filename)
        processing = True if metadata.get("bgs_processing") == "true" else False
        seconds += 1

    if not processing and notify:
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="grbl_frame_size",
                                                                            length=metadata.get("bgs_length"),
                                                                             width=metadata.get("bgs_width"),
                                                                             origin=metadata.get("bgs_origin")))
    else:
        _plugin._file_manager.remove_additional_metadata("local", filename, "bgs_processing")
        _plugin._logger.warning("gave up waiting for metadata processing")


def is_laser_mode(_plugin):
    try:
        if not is_grbl_fluidnc(_plugin):
            _plugin._logger.debug("_bgs: is_laser_mode={}".format(int(float(_plugin.grblSettings.get(32)[0])) != 0))
            return int(float(_plugin.grblSettings.get(32)[0])) != 0
        else:
            return not (_plugin.fluidYaml and _plugin.fluidYaml.get("laser") is None and _plugin.fluidYaml.get("Laser") is None and _plugin.fluidYaml.get("LASER") is None)
    except Exception as e:
        _plugin._logger.warn("_bgs: is_laser_mode: {}".format(e))

    return False

def is_grbl_one_dot_one(_plugin):
    oneDotOne = "VER:1." in _plugin.grblVersion and "VER:1.0" not in _plugin.grblVersion
    #_plugin._logger.debug("_bgs: is_grbl_one_dot_one result=[{}]".format(oneDotOne))
    return oneDotOne

def is_grbl_esp32(_plugin):
    oneDotOne = "VER:1." in _plugin.grblVersion and "VER:1.0" not in _plugin.grblVersion and "VER:1.1" not in _plugin.grblVersion
    #_plugin._logger.debug("_bgs: is_grbl_esp32 result=[{}]".format(oneDotOne))
    return oneDotOne

def is_grbl_fluidnc(_plugin):
    oneDotOne = " FLUIDNC " in _plugin.grblVersion.upper()
    #_plugin._logger.debug("_bgs: is_grbl_fluidnc result=[{}]".format(oneDotOne))
    return oneDotOne

def is_latin_encoding_available(_plugin):
    octoprintVersion = _plugin.octoprintVersion
    latinEncoding = int(octoprintVersion.split(".")[0]) > 1 or int(octoprintVersion.split(".")[1]) >= 8
    _plugin._logger.debug("_bgs: is_latin_encoding_available result=[{}]".format(latinEncoding))
    return latinEncoding


def do_fake_ack(printer, logger):
    time.sleep(1)
    printer.fake_ack()
    logger.debug("_bgs: do_fake_ack")


def send_command_now(printer, logger, cmd):
    try:
        printer.commands(cmd, force=True)
        logger.debug("_bgs: send_command")
    except Exception as e:
        logger.error("_bgs: send_command_now: %s" % e)


def defer_resuming_status_reports(_plugin, waitTime, showFinalize):
    if showFinalize:
        _plugin._plugin_manager.send_plugin_message(_plugin._identifier, dict(type="simple_notify",
                                                                title="Finalizing Changes. . .",
                                                                    text="Please wait while FluidNC's configuration and settings are finalized.",
                                                                    hide=True,
                                                                delay=15000,
                                                            notify_type="notice"))
    time.sleep(waitTime)
    _plugin.noStatusRequests = False


def update_fluid_config(_plugin):
    _plugin._logger.debug("_bgs: update_fluid_config")

    configName = _plugin.fluidSettings.get("Config/Filename", "config.yaml")
    _plugin._printer.commands("$LocalFS/Delete={}".format(configName))

    for key, value in _plugin.fluidYaml.items():
        process_fluid_config_item(_plugin, key, value)

    queue_cmds_and_send(_plugin, ["$CD={}".format(configName)])
    
def process_fluid_config_item(_plugin, key, value, path=""):
    if isinstance(value, dict):
        path = "{}{}/".format(path, key)
        for child_key, child_value in value.items():
            process_fluid_config_item(_plugin, child_key, child_value, path)
    else:
        if not value is None and not "PIN" in key.upper() and not "MOTOR" in path.upper() and not is_spindle(path):
            _plugin._printer.commands("$/{}{}={}".format(path, key, value.replace("null", "")))

def is_spindle(path):
    if path.upper().startswith("10V/"):
        return True
    elif path.upper().startswith("BESC/"):
        return True
    elif path.upper().startswith("DAC/"):
        return True
    elif path.upper().startswith("H2A/"):
        return True
    elif path.upper().startswith("H100/"):
        return True
    elif path.upper().startswith("HBRIDGE/"):
        return True
    elif path.upper().startswith("HUANYANG/"):
        return True
    elif path.upper().startswith("LASER/"):
        return True
    elif path.upper().startswith("NOWFOREVER/"):
        return True
    elif path.upper().startswith("NOSPINDLE/"):
        return True
    elif path.upper().startswith("ONOFF/"):
        return True
    elif path.upper().startswith("PWM/"):
        return True
    elif path.upper().startswith("RELAY/"):
        return True
    elif path.upper().startswith("YL620/"):
        return True

    return False

        
def get_axes_max_rates(_plugin):
    #_plugin._logger.debug("_bgs: get_axes_max_rates")
    
    # seed with defaults
    xf = 1000.0
    yf = 1000.0
    zf = 300.0

    try:
        if is_grbl_fluidnc(_plugin):
            xf = float(_plugin.fluidYaml.get("axes", {}).get("x", {}).get("max_rate_mm_per_min"))
            yf = float(_plugin.fluidYaml.get("axes", {}).get("y", {}).get("max_rate_mm_per_min"))
            zf = float(_plugin.fluidYaml.get("axes", {}).get("z", {}).get("max_rate_mm_per_min"))
        else:
            xf = float(_plugin.grblSettings.get(110)[0])
            yf = float(_plugin.grblSettings.get(111)[0])
            zf = float(_plugin.grblSettings.get(112)[0])
    except Exception as e:
        _plugin._logger.warn("_bgs: get_axes_max_rates: {}".format(e))

    #_plugin._logger.debug("_bgs: get_axes_max_rates x={} y={} z={}".format(xf, yf, zf))
    return xf, yf, zf


def get_axes_limits(_plugin):
    _plugin._logger.debug("_bgs: get_axes_limits")

    # seed with defaults
    xl = 200.0
    yl = 200.0
    zl = 50.0

    distance = 1

    try:
        if is_grbl_fluidnc(_plugin):
            xl = float(_plugin.fluidYaml.get("axes", {}).get("x", {}).get("max_travel_mm"))
            yl = float(_plugin.fluidYaml.get("axes", {}).get("y", {}).get("max_travel_mm"))
            zl = float(_plugin.fluidYaml.get("axes", {}).get("z", {}).get("max_travel_mm"))
        else:
            xl = float(_plugin.grblSettings.get(130)[0])
            yl = float(_plugin.grblSettings.get(131)[0])
            zl = float(_plugin.grblSettings.get(132)[0])

        # assign our default distance if it is not already set to the lower of x,y limits
        distance = float(_plugin._settings.get(["distance"]))

        if distance == 0 or distance > min([xl, yl]):
            distance = float(min([xl, yl]))

        _plugin._settings.set(["control_distance"], distance)
        _plugin._settings.save(trigger_event=True)
    except Exception as e:
        _plugin._logger.warn("_bgs: get_axes_limits: {}".format(e))

    _plugin._logger.debug("_bgs: get_axes_limits x={} y={} z={} distance={}".format(xl, yl, zl, distance))
    return xl, yl, zl