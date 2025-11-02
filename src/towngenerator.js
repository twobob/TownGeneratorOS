        var _gthis = this;
        com_watabou_coogee_Game.instance = this;
        openfl_display_Sprite.call(this);
        var initializeStage = function() {
                _gthis.prepareStage();
                com_watabou_utils_Updater.useRenderer(_gthis.stage.window);
                com_watabou_coogee_Game.switchScene(initScene);
                _gthis.layout();
        };
        if(this.stage != null) {
                initializeStage();
        } else {
                var onAdded = null;
                onAdded = function(_) {
                        _gthis.removeEventListener("addedToStage",onAdded);
                        initializeStage();
                };
                this.addEventListener("addedToStage",onAdded);
        }
        var _gthis = this;
        com_watabou_towngenerator_StateManager.pullParams();
        com_watabou_towngenerator_StateManager.pushParams();
        com_watabou_towngenerator_FontAssets.init();
        com_watabou_towngenerator_Main.uiFont = com_watabou_coogee_BitmapFont.get("font",com_watabou_towngenerator_mapping_CityMap.palette.paper);
        com_watabou_towngenerator_Main.uiFont.letterSpacing = 1;
        com_watabou_towngenerator_Main.uiFont.baseLine = 8;
        new com_watabou_towngenerator_building_Model(com_watabou_towngenerator_StateManager.size,com_watabou_towngenerator_StateManager.seed);
        com_watabou_coogee_Game.call(this,com_watabou_towngenerator_TownScene);
        var applyStageAppearance = function() {
                if(_gthis.stage != null) {
                        _gthis.stage.set_color(com_watabou_towngenerator_mapping_CityMap.palette.paper);
                }
        };
        if(this.stage != null) {
                applyStageAppearance();
        } else {
                var onAdded = null;
                onAdded = function(_) {
                        _gthis.removeEventListener("addedToStage",onAdded);
                        applyStageAppearance();
                };
                this.addEventListener("addedToStage",onAdded);
        }
        return new openfl_utils__$internal_TouchData();
        data.reset();
if(openfl_Lib.get_application() != null && openfl_Lib.get_current().stage != null) {
        com_watabou_towngenerator_Main.main();
}
